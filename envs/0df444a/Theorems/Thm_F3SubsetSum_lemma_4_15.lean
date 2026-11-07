-- Prove2me | Theorems.Thm_F3SubsetSum_lemma_4_15
-- name    : F3SubsetSum.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:46.868951+00:00
-- url     : https://prove2.me/theorems/6f54a561-240e-49b7-9cb0-fa4fca1da14e
-- title:
--   Lemma 4.15 — $\mathbb E[X_t\mid W_{t-1}]\ge\rho(W_{t-1})/3$
-- statement:
--   Let $q\ge3$ be prime and $D\ge2$. For every history $a_1,\dots,a_{t-1}\in\mathbb F_q^n$, with $W_{t-1}=V_{t-1}^\perp\subseteq R_D^*$ and a uniformly random new linear form $L_t$,
--
--   $$\mathbb E\bigl[X_t\mid W_{t-1}\bigr]\ge\frac{\rho(W_{t-1})}{3},$$
--
--   where $\rho$ is the symbolic rank (43). The symbolic rank is an upper bound for every specialised rank; this lemma says that a random specialisation keeps a third of it on average.
--
--   Differences from the source:
--   - encoding: the standing integer D ≥ 2 of §4.1 (eq. (29), p.18), left implicit in the statement → hypothesis D ≥ 2; reason: R*_{D−2} is undefined for D < 2 (natural-number subtraction would make it R*_0)
--   - encoding: E[X_t | W_{t−1}] → the average over the uniform new sample a_t for a fixed history; reason: X_t depends on the history only through W_{t−1} (Claim 4.14), so both conditionings give the same average
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Lemma 4.15, p.25

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_SampleImage
import Definitions.Def_F3SubsetSum_SymbolicRank

namespace F3SubsetSum

/-- **Lemma 4.15** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Lemma 4.15, p.25):
"For uniformly random L_t, we have E[X_t | W_{t−1}] ≥ ρ(W_{t−1})/3."

Over `F_q`, `q ≥ 3` prime, `D ≥ 2`: for every history `a_1, …, a_{t−1}`, the average over a
uniform new sample `a_t ∈ F_qⁿ` of the increment `X_t` (40) is at least one third of the symbolic
rank `ρ(W_{t−1})` (43), where `W_{t−1} = V_{t−1}^⊥ ⊆ R*_D`.

**Formalization Note** `X_t` depends on the history only through `W_{t−1}` (Claim 4.14), so
conditioning on `W_{t−1}` and conditioning on the history give the same average. -/
theorem lemma_4_15 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D) {t : ℕ}
    (a : Fin t → Fin n → ZMod q) :
    (symbolicRank (ZMod q) n q D (sampleImage q a D).dualAnnihilator : ℝ) / 3 ≤
      (∑ a' : Fin n → ZMod q, (increment q a a' D : ℝ)) / (q : ℝ) ^ n := by sorry

end F3SubsetSum
