-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_cases_1_3_deterministic
-- name    : BellDetEff.TwoParty.cases_1_3_deterministic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:14.030754+00:00
-- url     : https://prove2.me/theorems/4812d44f-7899-43ad-af07-7d2ed6b2e413
-- title:
--   Eqs. (7)–(12) — I_{M_A M_B (P+1)(P+1)} ≤ 0 for every deterministic local strategy
-- statement:
--   Let $P$ be a prime with $P\ge\max(M_A,M_B)$. Let $F$ map A's inputs $\{1,\dots,M_A\}$ to outputs in $\{0,\dots,P-1\}\cup\{\Phi\}$ and $G$ map B's inputs $\{1,\dots,M_B\}$ to outputs in $\{0,\dots,P-1\}\cup\{\Phi\}$, and let $p_{F,G}(a,b\mid x,y)=[F(x)=a]\,[G(y)=b]$ be the deterministic local behaviour (eq. (7)). Then the Bell expression of eq. (6) satisfies
--   $$I_{M_AM_B(P+1)(P+1)}(p_{F,G})\le 0.$$
--
--   This is the content of Cases 1–3 of the proof of Theorem 2 (the cases where A or B always outputs $\Phi$, where both answer on at least two inputs, and where one of them answers on exactly one input).
--
--   **Formalization Note** This states the conclusion of Case 3 as true. The middle equality of the paper's display (12) holds only when $G(y)\ne\Phi$ for every $y\ne 1$ (a $y$ with $G(y)=\Phi$ contributes $0$ rather than $-1$); the inequality $\le 0$ holds in every case. $P$ is any prime with $M_A,M_B\le P$, not only the minimal one.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, pp. 2–3, proof of Theorem 2, eqs. (7)–(12), Cases 1–3

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_BellInequality

namespace BellDetEff.TwoParty

/-- Cases 1–3, proof of Theorem 2 (Cao–Peng, arXiv:1607.04350v1, pp. 2–3, eqs. (7)–(12)): for a
prime `P ≥ max(MA, MB)` and every deterministic local strategy `F(x) = a`, `G(y) = b` with outputs
in `{0, …, P − 1} ∪ {Φ}`, the Bell expression (6) is at most `0`. -/
theorem cases_1_3_deterministic (P MA MB : ℕ) [Fact P.Prime] (hAP : MA ≤ P) (hBP : MB ≤ P)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P)) :
    bellValue P (deterministic F G) ≤ 0 := by sorry

end BellDetEff.TwoParty
