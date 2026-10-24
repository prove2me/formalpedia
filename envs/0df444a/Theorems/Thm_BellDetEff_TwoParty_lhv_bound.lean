-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_lhv_bound
-- name    : BellDetEff.TwoParty.lhv_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:01.246347+00:00
-- url     : https://prove2.me/theorems/0f9383ea-0d86-45e1-8303-e0191591b3a9
-- title:
--   Proof of Theorem 2 — every LHV behaviour satisfies I_{M_A M_B (P+1)(P+1)} ≤ 0
-- statement:
--   Let $P$ be a prime with $P\ge\max(M_A,M_B)$, and let $p$ be a behaviour with inputs $x\in\{1,\dots,M_A\}$, $y\in\{1,\dots,M_B\}$ and outputs in $\{0,\dots,P-1\}\cup\{\Phi\}$ for each party. If $p$ can be simulated by a local hidden variable model, i.e.
--   $$p(a,b\mid x,y)=\int_\Lambda p_A(a\mid x,\lambda)\,p_B(b\mid y,\lambda)\,d\mu(\lambda)$$
--   for some probability space $(\Lambda,\mu)$ and measurable local response probabilities, then
--   $$I_{M_AM_B(P+1)(P+1)}(p)\le 0 .$$
--
--   This is the local bound of the Bell inequality (6), the first half of the proof of Theorem 2. It holds for arbitrary hidden-variable spaces, not only for finite mixtures of deterministic strategies.
--
--   **Formalization Note** The marginals in the Bell expression are averages over the other party's input; for an LHV behaviour they agree with the marginal at every fixed input of the other party. $P$ is any prime with $M_A,M_B\le P$.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 2, proof of Theorem 2 ("First, we prove I ≤ 0 with LHV strategies")

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_BellInequality

namespace BellDetEff.TwoParty

/-- The LHV bound, proof of Theorem 2 (Cao–Peng, arXiv:1607.04350v1, p. 2): for a prime
`P ≥ max(MA, MB)`, every behaviour with outputs `{0, …, P − 1} ∪ {Φ}` that can be simulated by an
LHV model (eq. (3)) satisfies `I_{M_A M_B (P+1)(P+1)} ≤ 0`. -/
theorem lhv_bound (P MA MB : ℕ) [Fact P.Prime] (hAP : MA ≤ P) (hBP : MB ≤ P)
    (p : Option (Fin P) → Option (Fin P) → Fin MA → Fin MB → ℝ) (hp : LHVSimulable p) :
    bellValue P p ≤ 0 := by sorry

end BellDetEff.TwoParty
