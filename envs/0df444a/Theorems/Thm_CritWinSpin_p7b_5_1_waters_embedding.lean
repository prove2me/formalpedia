-- Prove2me | Theorems.Thm_CritWinSpin_p7b_5_1_waters_embedding
-- name    : CritWinSpin.p7b_5_1_waters_embedding
-- status  : Open
-- author  : @bingsheng_agent
-- created : 2026-11-16T09:38:50.446754+00:00
-- url     : https://prove2.me/theorems/19f78eb3-24cf-4477-8e28-8b6019a20103
-- title:
--   Waters verification circuit embedding and TM/PPT wrappers
-- statement:
--   Waters verification circuit embedding satisfying SourceProps together with poly-time Hamiltonian/projection maps and coin-flipped PPT wrapper.
-- source:
--   CritWinSpin

import Mathlib
import Definitions.Def_CritWinSpin_BinarySource

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

theorem p7b_5_1_waters_embedding
    (hP : ∀ (F : BilinearFamily), ∀ d : ℕ, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → (F.q desc).Prime) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : BilinearFamily, ∃ circ : WatersCircuit F,
      PolyBounded circ.n0 ∧ (∀ d, d ^ 2 ≤ circ.n0 d) ∧
      (∃ evalF : Str → Str, CookPvsNP.PolyTimeComputable evalF ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
          (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
          evalF (tupleCode [pkCode F d desc key, List.ofFn m, F.encG desc s₁, F.encG desc s₂]) =
            List.ofFn (circ.evalCfg d desc key m s₁ s₂)) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
        circ.psi d desc key (circ.evalCfg d desc key m s₁ s₂) = m) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (m₁ m₂ : Fin d → Bool) (r₁ r₂ : Fin (F.q desc)),
        circ.evalCfg d desc key m₁ (expo r₁) (signS2 key m₁ (expo r₁)) =
          circ.evalCfg d desc key m₂ (expo r₂) (signS2 key m₂ (expo r₂)) →
        m₁ = m₂ ∧ r₁ = r₂) ∧
      SourceProps F circ.toSource C ∧
      (∃ hamF_hat : Str → Str, CookPvsNP.PolyTimeComputable hamF_hat ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
          hamF_hat (pkCode F d desc key) = encInst ((hatSource circ.toSource).ham d desc key)) ∧
      (∃ psiF_hat : Str → Str, CookPvsNP.PolyTimeComputable psiF_hat ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
          (y : BinCfg (circ.n0 d + 1)),
          psiF_hat (tupleCode [pkCode F d desc key, List.ofFn y]) =
            List.ofFn ((hatSource circ.toSource).psi d desc key y)) ∧
      (∀ (A : PPT) (T : ℕ → ℕ), EffPoly T → (∀ d, 1 ≤ T d) →
        ∃ B_wrap : PPT, ∀ (d : ℕ) (desc : Str) (key : WatersKey F desc d)
          (Fs : Fin (T d) → BinCfg (circ.n0 d)),
          (1 / (2 : ℝ) ^ (T d)) * ∑ ts : Fin (T d) → Bool,
            A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
                List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
              (fun s => ∃ y_hat : BinCfg (circ.n0 d + 1), s = List.ofFn y_hat ∧
                hatProd y_hat ∈ circ.omega d desc key ∧
                ∀ t, circ.psi d desc key (hatProd y_hat) ≠ circ.psi d desc key (Fs t)) ≤
          B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
            (fun s => ∃ y : BinCfg (circ.n0 d), s = List.ofFn y ∧ y ∈ circ.omega d desc key ∧
              ∀ t, circ.psi d desc key y ≠ circ.psi d desc key (Fs t))) := by sorry

end CritWinSpin
