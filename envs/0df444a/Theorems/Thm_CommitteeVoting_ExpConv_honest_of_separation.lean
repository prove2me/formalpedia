-- Prove2me | Theorems.Thm_CommitteeVoting_ExpConv_honest_of_separation
-- name    : CommitteeVoting.ExpConv.honest_of_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:17.17307+00:00
-- url     : https://prove2.me/theorems/bf5fdd07-505f-497d-a927-20d3ef6bbee4
-- title:
--   Proof of Theorem 3, p. 48 — if every member of ℋ outscores every dishonest producer, the committee is honest
-- statement:
--   Let $k\le m$, let $0\le p\le 1$, let $\mathcal M$ be the set of dishonest producers, and let $\mathcal H$ be a set of producers disjoint from $\mathcal M$ (so every member of $\mathcal H$ is honest) with
--   $$|\mathcal H|\ \ge\ (1-p)\,k .$$
--   Let $s$ be any assignment of scores to the $m$ producers. If every member of $\mathcal H$ receives strictly more votes than every dishonest producer,
--   $$s(j_m) < s(j_h)\qquad\text{for all } j_h\in\mathcal H,\ j_m\in\mathcal M,$$
--   then the committee is honest: every admissible committee of size $k$ (ties and filling resolved adversarially) contains at least $\lceil (1-p)k\rceil$ producers outside $\mathcal M$.
--
--   This is the deterministic reduction with which the proof of Theorem 3 opens: it turns the event $\mathbb T=H$ into the event that all members of $\mathcal H$ outscore all members of $\mathcal M$, whose probability is then bounded by concentration.
--
--   **Formalization Note** The hypothesis $0\le p$ is the paper's implicit convention that $p$ is a fraction; without it the claim fails (with $\mathcal M=\emptyset$ and $p<0$ a committee of $k$ members cannot have $\lceil(1-p)k\rceil>k$ honest members). The honest candidates are the complement of $\mathcal M$; $\mathcal H$ need not be all of them.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 48, Proof of Theorem 3 (opening claim)

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee

namespace CommitteeVoting.ExpConv
theorem honest_of_separation {m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Mal H : Finset (Fin m)) (hdisj : Disjoint H Mal) (hcard : (1 - p) * (k : ℝ) ≤ (H.card : ℝ))
    (s : Fin m → ℕ) (hsep : ∀ jh ∈ H, ∀ jm ∈ Mal, s jm < s jh) :
    IsHonestOutcome k p Malᶜ s := by sorry
end CommitteeVoting.ExpConv
