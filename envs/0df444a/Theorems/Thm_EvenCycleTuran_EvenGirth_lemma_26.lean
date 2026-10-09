-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_lemma_26
-- name    : EvenCycleTuran.EvenGirth.lemma_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:12.359685+00:00
-- url     : https://prove2.me/theorems/af2701a8-7a33-4e4d-969c-213ad48dd2be
-- title:
--   Lemma 26, p. 19 — ex(n, C_{2k+1}, 𝒞_A) = Θ(ex(n, C_{2k+1}, 𝒞_{A∖O_k})), O_k the odd integers < 2k+1
-- statement:
--   Let $k\ge1$, let $A$ be a set of integers, each at least $3$, and let $O_k$ be the set of odd integers less than $2k+1$. Then
--
--   $$\mathrm{ex}(n,C_{2k+1},\mathcal C_A)=\Theta\big(\mathrm{ex}(n,C_{2k+1},\mathcal C_{A\setminus O_k})\big)\qquad(n\to\infty).$$
--
--   When an odd cycle is counted, forbidding shorter odd cycles in addition does not change the order of magnitude.
--
--   **Formalization Note.** $\Theta$ is Mathlib's `IsTheta` along `atTop`; $O_k$ is `{a | Odd a ∧ a < 2 * k + 1}`.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 19, Lemma 26

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem lemma_26 (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (hA : ∀ a ∈ A, 3 ≤ a) :
    (fun n : ℕ => (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * k + 1)) A : ℝ))
      =Θ[atTop] (fun n : ℕ =>
        (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * k + 1)) (A \ {a | Odd a ∧ a < 2 * k + 1}) : ℝ)) := by sorry

end EvenCycleTuran.EvenGirth
