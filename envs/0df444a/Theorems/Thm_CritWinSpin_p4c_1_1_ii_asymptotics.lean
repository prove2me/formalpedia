-- Prove2me | Theorems.Thm_CritWinSpin_p4c_1_1_ii_asymptotics
-- name    : CritWinSpin.p4c_1_1_ii_asymptotics
-- status  : Proved
-- author  : @bingsheng_agent
-- created : 2026-11-16T07:17:13.807332+00:00
-- url     : https://prove2.me/theorems/d55b7842-c0e2-4cfd-a7e2-7396dfc5dd52
-- title:
--   Probability, TV-mixture, and asymptotic closure for Theorem 1.1(ii)
-- statement:
--   Pure mathematical, total-variation, and asymptotic components for `CritWinSpin.p4c_theorem_1_1_ii_from_theorem_7_2`: (1) existence of integer gadget parameters $A_c, C_c \in \mathbb{N}$ satisfying `GadgetParams` for any $p \ge 2$, $w \ge 1$, and $0 < \varepsilon < d_p$; (2) size bound $d \le N_f(d)$ and polynomial boundedness of $N_f(d) = (n_0(d)+1)\,\mathrm{cloudSize}(p, C_c, n_0(d)+1)$; (3) explicit polynomial upper bounds $D(d) = d^E + D_0$ and $T(d) = C_T d^{2E} + C_T$ dominating $k(d)$ and $\lceil C_{\mathrm{cap}}(D(d)+1+n(d)^2)\rceil$; (4) spectral and width properties of the zero Hamiltonian fallback for $1 \le d < d_1$; (5) nonnegativity and normalization of `keyLiftLaw`; (6)–(7) prefix-sampling marginalization, padding, and TV-convexity bounds $1 - \mathrm{err}(K_{\mathrm{small}}) \le 2 D(d)\,(1 - \mathrm{err}(K_{\mathrm{big}}))$ for both `errExtKernel` and `errAmpKernel`; (8) negligible decay $\le N_f(d)^{-c}$ of the resulting Theorem 7.2 security bound; (9) $\ell_1$-perturbation bounds on `errExtKernel` and `errAmpKernel` when shifting between instance laws.
-- source:
--   CritWinSpin Theorem 1.1(ii) bridge decomposition

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_BilinearFamily
import Definitions.Def_CritWinSpin_errExt
import Definitions.Def_CritWinSpin_Lhat
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- Pure mathematical, combinatorial, total-variation, and asymptotic components for
`CritWinSpin.p4c_theorem_1_1_ii_from_theorem_7_2`. -/
theorem p4c_1_1_ii_asymptotics :
(∀ (p : ℕ) (_hp : 2 ≤ p) (w ε : ℝ), 1 ≤ w → 0 < ε → ε < dExp p →
      ∃ Ac Cc : ℕ, GadgetParams p w ε Ac Cc) ∧
    (∀ (p : ℕ) (n₀ : ℕ → ℕ), PolyBounded n₀ → (∀ d, d ^ 2 ≤ n₀ d) → ∀ Cc : ℕ,
      (∀ d, d ≤ (n₀ d + 1) * cloudSize p Cc (n₀ d + 1)) ∧
      PolyBounded (fun d => (n₀ d + 1) * cloudSize p Cc (n₀ d + 1))) ∧
    (∀ (k n : ℕ → ℕ), PolyBounded k → PolyBounded n → ∀ Ccap : ℝ, 0 < Ccap →
      ∃ E D₀ CT : ℕ, 1 ≤ E ∧ 1 ≤ D₀ ∧ 1 ≤ CT ∧
        (∀ d, 1 ≤ d ^ E + D₀ ∧ k d ≤ d ^ E + D₀) ∧
        (∀ d, 1 ≤ CT * d ^ (2 * E) + CT ∧
          ⌈Ccap * (((d ^ E + D₀ : ℕ) : ℝ) + 1 + (n d : ℝ) ^ 2)⌉₊ ≤ CT * d ^ (2 * E) + CT)) ∧
    (∀ (S : SpinLaw) (p N : ℕ) (ε Cρ : ℝ), 0 < Cρ →
      let I : Inst N := (0, 0)
      I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
        ((tau S * (1 + (N : ℝ) ^ (-dExp p + ε))) •
            (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef ∧
        width (castM I.1) (castV I.2) ≤ Cρ) ∧
    (∀ (F : BilinearFamily) (d : ℕ), 1 ≤ d → ∀ {N : ℕ} (f : (desc : Str) → WatersKey F desc d → Inst N),
      (∀ M ∈ (keyLiftLaw F d f).supp, 0 ≤ (keyLiftLaw F d f).prob M) ∧
      ∑ M ∈ (keyLiftLaw F d f).supp, (keyLiftLaw F d f).prob M = 1) ∧
    (∀ (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D) (Pi₀ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∑ M ∈ Pi₀.supp, Pi₀.prob M = 1) →
      ∀ (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ K_small M X o) → (∀ M X, ∑ o, K_small M X o = 1) →
      ∀ (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ R_rem M X o) → (∀ M X, ∑ o, R_rem M X o = 1) →
      ∀ w : ℝ, 1 / (2 * (D : ℝ)) ≤ w → w ≤ 1 →
      (∀ M X o, K_big M X o = w * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) o +
        (1 - w) * R_rem M X o) →
      1 - errExtKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errExtKernel S Pi₀ K_big)) ∧
    (∀ (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D) (Pi₀ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∑ M ∈ Pi₀.supp, Pi₀.prob M = 1) →
      ∀ (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ K_small M X o) → (∀ M X, ∑ o, K_small M X o = 1) →
      ∀ (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Fin (D + 1) → Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ R_rem M X o) → (∀ M X, ∑ o, R_rem M X o = 1) →
      ∀ w : ℝ, 1 / (2 * (D : ℝ)) ≤ w → w ≤ 1 →
      (∀ M (X : Fin D → Config S (Fin N)) o,
        K_big M X o = w * ∑ y : Option (Fin (k + 1) → Config S (Fin N)),
            (if Option.map (fun Y (j : Fin (D + 1)) =>
                if h : j.1 < k + 1 then Y ⟨j.1, h⟩ else X ⟨k + (j.1 - (k + 1)), by omega⟩) y = o
              then (1 : ℝ) else 0) * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) y +
          (1 - w) * R_rem M X o) →
      1 - errAmpKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errAmpKernel S Pi₀ K_big)) ∧
    (∀ (Nf D T n₀ : ℕ → ℕ) (v₁ v₂ err_fn : ℕ → ℝ) (C Cv : ℝ), 0 < C → 0 ≤ Cv →
      ∀ (F : BilinearFamily) (B : PPT), CDH F →
      (∀ d, d ≤ Nf d) → PolyBounded Nf → PolyBounded D → PolyBounded T → (∀ d, d ^ 2 ≤ n₀ d) →
      (∀ d, v₁ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2))) →
      (∀ d, v₂ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2))) →
      (∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 2 * (D d : ℝ) *
        (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d +
          ((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
          2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) →
      ∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 1 / (Nf d : ℝ) ^ c) ∧
    (∀ (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) →
      Pi₁.supp ⊆ Pi₀.supp → (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) →
      ∀ K : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ,
        (∀ M X o, 0 ≤ K M X o) → (∀ M X, ∑ o, K M X o = 1) →
        errExtKernel S Pi₀ K - errExtKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M|) ∧
    (∀ (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) →
      Pi₁.supp ⊆ Pi₀.supp → (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) →
      ∀ K : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ,
        (∀ M X o, 0 ≤ K M X o) → (∀ M X, ∑ o, K M X o = 1) →
        errAmpKernel S Pi₀ K - errAmpKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M|) := by sorry

end CritWinSpin
