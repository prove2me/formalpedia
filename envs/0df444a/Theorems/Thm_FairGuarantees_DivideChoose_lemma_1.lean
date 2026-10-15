-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_lemma_1
-- name    : FairGuarantees.DivideChoose.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:33.32011+00:00
-- url     : https://prove2.me/theorems/af293a61-75b5-49f4-abf5-e53fe6a8992b
-- title:
--   Lemma 1, p. 10 — every share S has an n-equipartition for every u ∈ D(Ω)
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ ($d\ge1$) be a manna, $u\in\mathcal D(\Omega)$ a utility, $S$ a share and $n\ge1$. Then the set of $n$-equipartitions of $S$ at $u$ is nonempty:
--   $$\mathcal{EP}_n(S;u)\neq\emptyset .$$
--
--   The utility $u$ may be non-monotone and take both signs. This is the step that lets the current Divider of the Divide & Choose rule cut the remaining manna into equally valued pieces.
--
--   **Formalization Note** The hypothesis $d\ge1$ is the paper's standing assumption that Lebesgue measure on the Euclidean space is non-atomic (§3, "Non atomic fair division"). On $\mathbb R^0$, a single point of measure $1$, the statement fails.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 10, §3.2, Lemma 1

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

namespace FairGuarantees.DivideChoose

/-- Lemma 1, p. 10: for every share `S` and every utility `u ∈ D(Ω)` (neither monotone nor of
constant sign), the set `EP_n(S; u)` of `n`-equipartitions of `S` is nonempty. -/
theorem lemma_1 {d n : ℕ} (hd : 0 < d) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {S : Set (E d)} (hS : IsShare Ω S) (hn : 0 < n) :
    ∃ P : Fin n → Set (E d), IsEquipartition Ω u S n P := by sorry

end FairGuarantees.DivideChoose
