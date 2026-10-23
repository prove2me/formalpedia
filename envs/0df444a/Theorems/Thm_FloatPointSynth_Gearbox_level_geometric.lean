-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_level_geometric
-- name    : FloatPointSynth.Gearbox.level_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:21.829821+00:00
-- url     : https://prove2.me/theorems/28bdcd1f-e562-4daf-a4aa-7069df4a1abd
-- title:
--   Appendix A, p. 14 — the level-q success probability is P_q, and N_q is geometric with mean 1/P_q and variance (1 − P_q)/P_q²
-- statement:
--   Let $U$ be a single-qubit unitary and $\theta_0\in[0,\pi/2]$ with $\sin^2\theta_0=|U_{1,0}|^2$. For every level $q\ge1$:
--
--   1. the probability $p_q(U)$ that the level-$q$ measurement of the composed gearbox circuit succeeds equals
--   $$P_q=\sin^4(\varphi_q)+\cos^4(\varphi_q),\qquad \varphi_q=\tan^{-1}\big(\tan^{2^{q-1}}(\theta_0)\big);$$
--   2. the number $N_q$ of times the level-$q$ measurement is applied, geometrically distributed on $\{1,2,\dots\}$ with success probability $p_q(U)$, has mean
--   $$\mathbb E(N_q)=\frac1{P_q};$$
--   3. and variance
--   $$\mathbb V(N_q)=\frac{1-P_q}{P_q^2}.$$
--
--   Part 1 is where Theorem 1 and Corollary 1 enter the cost analysis: it identifies the circuit's success probabilities with the closed forms in which Theorem 2 is stated.
--
--   **Formalization Note** Means and variances are in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: "$N_q$ is geometrically distributed with mean $1/P_q$ and variance $(1-P_q)/P_q^2$", where $P_q$ is used as the success probability of the level-$q$ measurement → part 1 states explicitly that the Born success probability computed from the circuit equals $P_q$, and parts 2–3 compute the moments of the geometric law with that probability; reason: the paper identifies the two implicitly (Corollary 2's proof, p. 6: "$P_d$ is the probability of the measurement succeeding").
--   - encoding: "for all $q\le d$" → for every $q\ge1$; reason: $d$ is arbitrary, so the two are the same set of statements.
--   - encoding: real mean and variance → `ℝ≥0∞`-valued moments equal to `ENNReal.ofReal` of the real values; reason: the values are finite and positive, so nothing changes.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 14, Appendix A, proof of Theorem 2 (first paragraph)

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

namespace FloatPointSynth.Gearbox

/-- Appendix A, p. 14. For unitary `U` and `θ0 ∈ [0, π/2]` with `sin²θ0 = |U_{1,0}|²`, and every
level `q ≥ 1`: the level-`q` success probability of the circuit is `P_q`, and the number `N_q` of
level-`q` trials (geometric on `{1, 2, …}`) has mean `1/P_q` and variance `(1 - P_q)/P_q²`. -/
theorem level_geometric (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 ≤ Real.pi / 2) (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2)
    (q : ℕ) (hq : 1 ≤ q) :
    levelProb U q = P θ0 q ∧
    pmfMean (geomPos (levelProb U q)) = ENNReal.ofReal (1 / P θ0 q) ∧
    pmfVar (geomPos (levelProb U q)) = ENNReal.ofReal ((1 - P θ0 q) / P θ0 q ^ 2) := by sorry

end FloatPointSynth.Gearbox
