-- Prove2me | Theorems.Thm_DataDepProb_Discrete_lemma_C_2
-- name    : DataDepProb.Discrete.lemma_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:12:28.672069+00:00
-- url     : https://prove2.me/theorems/c574085d-ac86-498b-9eba-1c8450c71914
-- title:
--   Lemma C.2 — $\ell_1$ accuracy $\tau/(c_1+c_2)$ gives duality gap at most $\tau$
-- statement:
--   For the inputs of Appendix C ($\eta>0$, $\lambda\ge0$, $q^+=\mathrm{MW}_\eta(q,f,b)$, $e=e_s$), let $p^*$ minimize $A_s(p)=\mathrm{KL}(p\|q^+)+8\lambda H(p-e)^2$ over $\tilde\Delta_d$ and set
--   $$c_1=\Lambda+\eta+16\lambda\Gamma\log(1+d),\qquad c_2=2d+16\lambda\big(\Gamma^2+4d\log(1+d)\big).$$
--   Every $\hat p\in\tilde\Delta_d$ with $\|\hat p-p^*\|_1\le\tau/(c_1+c_2)$ has duality gap at most $\tau$: $\langle\nabla A_s(\hat p),\hat p-w\rangle\le\tau$ for every $w\in\tilde\Delta_d$.
--
--   Differences from the source:
--   - reading: the standing inputs of Appendix C → `ProjInput η qplus e`, `0 < η`, `0 ≤ lam`; reason: Appendix C's section assumption.
--   - encoding: $\langle\nabla A_s(\hat p),\hat p-w\rangle$ and the max over $w$ → `fderiv ℝ (objA lam qplus e) phat (phat - w) ≤ τ` for every `w ∈ ∆̃_d`; reason: the gradient pairing is the Fréchet derivative.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 37, Lemma C.2 (proof pp. 39–40)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_ScalarReduction

namespace DataDepProb.Discrete

/-- Lemma C.2 (from `ℓ₁` accuracy to duality gap, p. 37). For the inputs of Appendix C
(`η > 0`, `λ ≥ 0`, `q⁺ = MW_η(q, f, b)`, `e = e_s`), let `p*` minimize
`A_s(p) = KL(p‖q⁺) + 8λH(p − e)²` over `∆̃_d` and set `c₁ = Λ + η + 16λΓ log(1 + d)`,
`c₂ = 2d + 16λ(Γ² + 4d log(1 + d))`. Every `p̂ ∈ ∆̃_d` with `‖p̂ − p*‖₁ ≤ τ/(c₁ + c₂)` has duality
gap `max_{w ∈ ∆̃_d} ⟨∇A_s(p̂), p̂ − w⟩ ≤ τ`. -/
theorem lemma_C_2 {d : ℕ} (η lam τ : ℝ) (hη : 0 < η) (hlam : 0 ≤ lam) (qplus e : Fin d → ℝ)
    (hin : ProjInput η qplus e) (pstar : Fin d → ℝ) (hps : pstar ∈ truncSimplex d)
    (hmin : IsMinOn (objA lam qplus e) (truncSimplex d) pstar)
    (phat : Fin d → ℝ) (hph : phat ∈ truncSimplex d)
    (hclose : l1dist phat pstar ≤
      τ / ((LambdaC d + η + 16 * lam * gammaC d * Real.log (1 + (d : ℝ))) +
        (2 * d + 16 * lam * (gammaC d ^ 2 + 4 * d * Real.log (1 + (d : ℝ)))))) :
    ∀ w ∈ truncSimplex d, fderiv ℝ (objA lam qplus e) phat (phat - w) ≤ τ := by sorry

end DataDepProb.Discrete
