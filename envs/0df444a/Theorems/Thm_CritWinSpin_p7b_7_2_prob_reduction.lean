-- Prove2me | Theorems.Thm_CritWinSpin_p7b_7_2_prob_reduction
-- name    : CritWinSpin.p7b_7_2_prob_reduction
-- status  : Proved
-- author  : @bingsheng_agent
-- created : 2026-11-16T06:26:23.331322+00:00
-- url     : https://prove2.me/theorems/98e94cb6-99e5-4d65-a05e-c6b808504dab
-- title:
--   Probability and combinatorics reduction for Theorem 7.2
-- statement:
--   Reduces extension and amplification advantage bounds for arbitrary stochastic kernels K_ext and K_amp to the key-averaged simulated forging scores score_ext and score_amp plus the uniform-message, collision, source TV, and Lhat TV errors.
-- source:
--   CritWinSpin Theorem 7.2 decomposition

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- Pure probability and combinatorics reduction for Theorem 7.2: reduces extension and
amplification advantage bounds for arbitrary stochastic kernels `K_ext` and `K_amp` to the
key-averaged simulated forging scores `score_ext` and `score_amp` plus the uniform-message,
collision, source TV, and `Lhat` TV errors. -/
theorem p7b_7_2_prob_reduction (S : SpinLaw) (p : ℕ)
    (F : BilinearFamily) (src : BinarySource F) (C : ℝ) (hsrc : SourceProps F src C)
    (Ac Cc : ℕ) (slotM : PPT)
    (û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ) (d₁ : ℕ)
    (hdec : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      LhatDecodes (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key)))
    (k T : ℕ → ℕ) (hT1 : ∀ d, 1 ≤ T d) (v₁ v₂ : ℕ → ℝ)
    (hv₁ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d)) ≤ v₁ d)
    (hv₂ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d + 1))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d + 1)) ≤ v₂ d)
    (K_ext : (d : ℕ) → Inst (src.n d * cloudSize p Cc (src.n d)) →
      (Fin (k d) → Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) →
      Option (Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) → ℝ)
    (hKe0 : ∀ d M X o, 0 ≤ K_ext d M X o) (hKe1 : ∀ d M X, ∑ o, K_ext d M X o = 1)
    (K_amp : (d : ℕ) → Inst (src.n d * cloudSize p Cc (src.n d)) →
      (Fin (k d) → Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) →
      Option (Fin (k d + 1) → Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) → ℝ)
    (hKa0 : ∀ d M X o, 0 ≤ K_amp d M X o) (hKa1 : ∀ d M X, ∑ o, K_amp d M X o = 1)
    (score_ext score_amp : (d : ℕ) → (desc : Str) → WatersKey F desc d →
      (Fin (T d) → BinCfg (src.n d)) → ℝ)
    (hscore_ext : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      ∀ Fs : Fin (T d) → BinCfg (src.n d),
      (∑ ω : Fin (T d) → Option (Config S (Fin (src.n d) × Fin (cloudSize p Cc (src.n d)))),
        (∏ t, slotKernel S p Cc slotM (src.ham d desc key) (û d desc key) (Fs t) (ω t)) *
          match lhatRun (k d) ω with
          | none => 0
          | some R =>
            ∑ y : Config S (Fin (src.n d) × Fin (cloudSize p Cc (src.n d))),
              K_ext d (liftInst S p Ac Cc (src.ham d desc key) (û d desc key))
                (fun j a => (R j).2 (finProdFinEquiv.symm a))
                (some (fun a => y (finProdFinEquiv.symm a))) *
              (match List.findSome? (fun j =>
                  match decodeY ((Fin.cons y (fun j' => (R j').2) : Fin (k d + 1) → Config S (Fin (src.n d) × Fin (cloudSize p Cc (src.n d)))) j) with
                  | some y₀ => if ∃ j' : Fin (k d), decMsg (src.psi d desc key) (R j').2 = some (src.psi d desc key y₀) then none else some y₀
                  | none => none) (List.finRange (k d + 1)) with
               | none => 0
               | some y₀ => if y₀ ∈ src.omega d desc key ∧ ∀ t : Fin (T d), src.psi d desc key y₀ ≠ src.psi d desc key (Fs t) then 1 else 0)) ≤
        score_ext d desc key Fs)
    (hscore_amp : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      ∀ Fs : Fin (T d) → BinCfg (src.n d),
      (∑ ω : Fin (T d) → Option (Config S (Fin (src.n d) × Fin (cloudSize p Cc (src.n d)))),
        (∏ t, slotKernel S p Cc slotM (src.ham d desc key) (û d desc key) (Fs t) (ω t)) *
          match lhatRun (k d) ω with
          | none => 0
          | some R =>
            ∑ X' : Fin (k d + 1) → Config S (Fin (src.n d) × Fin (cloudSize p Cc (src.n d))),
              K_amp d (liftInst S p Ac Cc (src.ham d desc key) (û d desc key))
                (fun j a => (R j).2 (finProdFinEquiv.symm a))
                (some (fun j a => X' j (finProdFinEquiv.symm a))) *
              (match List.findSome? (fun j =>
                  match decodeY (X' j) with
                  | some y₀ => if ∃ j' : Fin (k d), decMsg (src.psi d desc key) (R j').2 = some (src.psi d desc key y₀) then none else some y₀
                  | none => none) (List.finRange (k d + 1)) with
               | none => 0
               | some y₀ => if y₀ ∈ src.omega d desc key ∧ ∀ t : Fin (T d), src.psi d desc key y₀ ≠ src.psi d desc key (Fs t) then 1 else 0)) ≤
        score_amp d desc key Fs) :
    ∀ d ≥ max 1 d₁,
      let Pi₀ := keyLiftLaw F d fun desc key => liftInst S p Ac Cc (src.ham d desc key) (û d desc key)
      (1 - keygenAvg F d (fun desc key => ∑ Fs, prodLaw (unifOn (src.omega d desc key)) Fs * score_ext d desc key Fs) -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errExtKernel S Pi₀ (K_ext d)) ∧
      (1 - keygenAvg F d (fun desc key => ∑ Fs, prodLaw (unifOn (src.omega d desc key)) Fs * score_amp d desc key Fs) -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errAmpKernel S Pi₀ (K_amp d)) := by sorry

end CritWinSpin
