-- Prove2me | Theorems.Thm_ConstrSOSP_corollary_5_6
-- name    : ConstrSOSP.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:08:23.428247+00:00
-- url     : https://prove2.me/theorems/cd44fe96-bacb-4726-8f9b-101ad4e108bb
-- title:
--   Corollary 5.6: hardness with constant separation from the boundary
-- statement:
--   **Theorem.** There is $K_0$ such that for every clock exponent $K\ge K_0$ there is a polynomial-time reduction from Iter to Interior-Sosp on $[0,1]^2$ under the restrictions of Theorem 5.1: 1-Lipschitz, 1-smooth and 1-Hessian-Lipschitz objectives, accuracy $(\epsilon,\sqrt\epsilon)$, and every $\epsilon$-approximate KKT point in $[1/12,11/12]^2$. Moreover, on every Iter instance with $N=6\cdot2^n+6\ge10^{40}$ the reduction writes
--   $$
--   \epsilon=\frac{\epsilon_0^2}{c_0^2N^4},\qquad \sqrt\epsilon=\frac{\epsilon_0}{c_0N^2},\qquad c_0=2^{76},\ \epsilon_0=10^{-10},
--   $$
--   and machines whose outputs at every rational point of $[0,1]^2$ are the value, gradient and Hessian of the normalized function $F$.
--
--   With Iter's PLS-hardness this is the first conjunct of Theorem 5.1.
--
--   **Formalization Note** The reduction is given explicitly so that its accuracy and its function can be stated. Smaller Iter instances are solved directly by the reduction (p.36).
--
--   Differences from the source:
--   - reading: "remains PLS-hard" → Iter reduces to the problem in polynomial time; reason: the paper proves PLS-hardness by this reduction from the PLS-complete Iter (p.22: "We first give a polynomial-time reduction from Iter to Interior-Sosp")
--   - reading: "Turing machine for f" running in polynomial time (p.17) → a machine code run for T·(|w|+1)^K steps, with T written in unary in the instance and the exponent K fixed by the problem; the statement holds for every K ≥ K₀; reason: the paper leaves the time bound implicit; an instance-chosen exponent or a binary clock would let a reduction hide exponential work, so the fixed-exponent unary clock is the faithful reading
--   - reading: ‖∇²f(x) − ∇²f(y)‖ with an unspecified matrix norm (Definitions 4.6, 4.8, 4.10) → Frobenius norm; reason: the norm of the proof of Lemma 5.4 ("Throughout the proof, matrix norms are Frobenius norms", p.49); it bounds the spectral norm, so the promise is the stronger one
--   - encoding: white-box functions given by polynomial-time Turing machines (p.17) → machine codes of Cook Turing machines, evaluated on binary codes of rational points (encRatVec), outputs as binary rationals (encRat, encRatVec, encRatMatrix); reason: p.17 fixes rational white-box semantics; Lean convention; same instances
--   - encoding: promises and answers at points of [0, 1]² → promises quantified over rational points; answers are rational points; reason: p.17: f(x), ∇f(x), ∇²f(x) at rational inputs denote the machines' rational outputs and the Lipschitz and Taylor conditions refer to these maps
--   - encoding: instances list A, B, L, L₁, L₂ and accept violation certificates (Definitions 4.6, 4.8, 4.10) → A = [I; −I], B = (1, 1, 0, 0), L = L₁ = L₂ = 1 are fixed and not written; violation certificates are not answers; reason: Theorem 5.1 fixes these data; on a valid instance the promises exclude every Lipschitz and Taylor violation and the KKT margin excludes a boundary SOSP1, so the answer sets coincide
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Corollary 5.6, p.55 (proof pp.55–57)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ConstrSOSP_Iter
import Definitions.Def_ConstrSOSP_InteriorSospBox
import Definitions.Def_ConstrSOSP_encInst
import Definitions.Def_ConstrSOSP_Evals
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_epsF
import Definitions.Def_ConstrSOSP_sqrtEpsF
import Definitions.Def_ConstrSOSP_Fnorm
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_app
import Definitions.Def_ConstrSOSP_encCircuit

namespace ConstrSOSP

/-- **Corollary 5.6** (arXiv:2604.02285, 2 Nov 2026, p.55): "(Hardness with constant separation
from the boundary). Finding an (ϵ, √ϵ)-SOSP remains PLS-hard on [0, 1]^2 for 1-Lipschitz,
1-smooth, and 1-Hessian-Lipschitz objectives, even under the promise that every ϵ-approximate KKT
point belongs to [1/12, 11/12]^2, where c0 = 2^76 and ϵ = ϵ0^2/(c0^2 N^4). The proximal gradient
uses smoothness bound 1."

There is `K₀` such that for every clock exponent `K ≥ K₀` there are polynomial-time instance and
answer maps (Cook's Turing machines) reducing Iter to Interior-Sosp on `[0, 1]²` (`ValidBox K`:
`L = L₁ = L₂ = 1`, accuracy `(ϵ, √ϵ)`, all regularity promises, KKT margin `[1/12, 11/12]²`),
correct for every answer; and on every Iter instance `C` with `N = 6·2ⁿ + 6 ≥ 10⁴⁰` the instance
map writes the accuracies `ϵ = ϵ₀²/(c₀²N⁴)`, `√ϵ = ϵ₀/(c₀N²)` and machines whose outputs at
every rational point of `[0, 1]²` are the value, gradient and Hessian of the normalized function
`F = Fnorm C`.

**Formalization Note** The reduction is given explicitly (`red`, `dec`) so that its accuracy and
its function can be stated; the first conjunct block is `SearchReduces Iter (InteriorSospBox K)`
unfolded. Instances with `N < 10⁴⁰` are left to the reduction ("the finitely many smaller Iter
instances can be solved directly", p.36). -/
theorem corollary_5_6 :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∃ (red : List Bool → List Bool) (dec : List (Option (Bool ⊕ Bool)) → List Bool),
        CookPvsNP.PolyTimeComputable red ∧ CookPvsNP.PolyTimeComputable dec ∧
        (∀ s, Iter.valid s → (InteriorSospBox K).valid (red s) ∧
          ∀ t, (InteriorSospBox K).answer (red s) t →
            Iter.answer s (dec (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)))) ∧
        ∀ C : Circuit, C.WF → 1 < C.app 1 → 10 ^ 40 ≤ gridN C.n →
          ∃ (T : ℕ) (cf cg cH : List Bool),
            red (encCircuit C) =
              encInst (epsF (gridN C.n)) (sqrtEpsF (gridN C.n)) T cf cg cH ∧
            ∀ x : Fin 2 → ℚ, (fun i => (x i : ℝ)) ∈ Poly boxA boxB →
              ∀ (v : ℚ) (g : Fin 2 → ℚ) (H : Fin 2 → Fin 2 → ℚ), Evals K T cf cg cH x v g H →
                (v : ℝ) = Fnorm C (fun i => (x i : ℝ)) ∧
                (∀ i, (g i : ℝ) = gradVec (Fnorm C) (fun i => (x i : ℝ)) i) ∧
                ∀ i j, (H i j : ℝ) = hessMat (Fnorm C) (fun i => (x i : ℝ)) i j := by sorry

end ConstrSOSP
