-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_lemma_25
-- name    : EvenCycleTuran.EvenGirth.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:57.78495+00:00
-- url     : https://prove2.me/theorems/3034ffe3-4109-4dd0-a620-22997c7d4d45
-- title:
--   Lemma 25, p. 18 — if 2k ∉ A then ex(n, C₂ₖ, 𝒞_A) = Θ(ex(n, C₂ₖ, 𝒞_{A_e}))
-- statement:
--   Let $k\ge 2$ and let $A$ be a set of integers, each at least $3$, with $2k\notin A$. Let $A_e$ be the set of even numbers in $A$. Then
--
--   $$\mathrm{ex}(n,C_{2k},\mathcal C_A)=\Theta\big(\mathrm{ex}(n,C_{2k},\mathcal C_{A_e})\big)\qquad(n\to\infty).$$
--
--   So when an even cycle is counted, forbidding odd cycles in addition does not change the order of magnitude of the generalized Turán number. In the proof of Theorem 14 it allows the extremal graph to be assumed bipartite.
--
--   **Formalization Note.** $\Theta$ is Mathlib's `IsTheta` along `atTop` for the two functions of $n$ cast to $\mathbb R$; the constants may depend on $k$ and $A$. $A_e$ is `{a ∈ A | Even a}`.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 18, Lemma 25 (A_e defined on p. 7 and p. 18)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem lemma_25 (k : ℕ) (hk : 2 ≤ k) (A : Set ℕ) (hA : ∀ a ∈ A, 3 ≤ a) (h2k : 2 * k ∉ A) :
    (fun n : ℕ => (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * k)) A : ℝ))
      =Θ[atTop] (fun n : ℕ => (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * k)) {a ∈ A | Even a} : ℝ)) := by sorry

end EvenCycleTuran.EvenGirth
