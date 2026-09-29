-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_double_pseudoExtreme
-- name    : EdmondsKarp.Scaling.double_pseudoExtreme
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:26:12.201961+00:00
-- url     : https://prove2.me/theorems/71090eb8-939e-45e9-9f21-a4d477a36092
-- title:
--   Lemma 3 — if $f$ is pseudo-extreme in Problem $p$, then $2f$ is pseudo-extreme in Problem $p-1$
-- statement:
--   Let $a_1,\dots,a_m$ and $b_1,\dots,b_n$ be positive integers with $\sum_i a_i = \sum_j b_j$ ($m, n \ge 1$) and let $d_{ij} \ge 0$ be costs. For $p \ge 1$, if $f$ is a pseudo-extreme flow in Problem $p$ (capacities $\lfloor a_i/2^p\rfloor$ and $\lfloor b_j/2^p\rfloor$), then $2f$ is a pseudo-extreme flow in Problem $p-1$ (capacities $\lfloor a_i/2^{p-1}\rfloor$ and $\lfloor b_j/2^{p-1}\rfloor$).
--
--   In particular $2f$ is a flow of Problem $p-1$. This is what allows the scaling method to start each phase from twice the final flow of the previous phase.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 260, Lemma 3

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Lemma 3 (p. 260): if `f` is a pseudo-extreme flow in Problem `p` (`p ≥ 1`), then `2f` is a
pseudo-extreme flow in Problem `p - 1`. -/
theorem double_pseudoExtreme {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (p : ℕ) (hp : 1 ≤ p) (x : Flow m n)
    (hx : IsPseudoExtreme (problem a b d p) x) :
    IsPseudoExtreme (problem a b d (p - 1)) ((2 : ℝ) • x) := by sorry

end EdmondsKarp.Scaling
