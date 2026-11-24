-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_Supplement_matching_regret
-- name    : BayesProphet.MultiSec.Supplement.matching_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:10:56.733803+00:00
-- url     : https://prove2.me/theorems/e61d178b-0f6e-4975-b0b0-15600225f3d7
-- title:
--   Theorem 4 — constant regret of the Fluid Bayes Selector for Online Matching
-- statement:
--   Consider Online Matching with $d$ resources, $n$ types, adjacency matrix $A\in\{0,1\}^{d\times n}$, rewards $r\in\mathbb R^{d\times n}_{\ge0}$, $S_j=\{i:a_{ij}=1\}$ and $r_{\max}=\max_{i,j}r_{ij}a_{ij}$. Let the arrival law over $T$ periods satisfy Eq. (14): for every $j$ there are $c_j\ge0$ and $\tau_j\in\mathbb N$ with
--   $$\mathbb P\Big[\|Z(t)-\mathbb E Z(t)\|_1\ \ge\ \frac{\mathbb E[Z_j(t)]}{|S_j|+1}\Big]\ \le\ \frac{c_j}{t^2}\qquad\forall t\in[T],\ t>\tau_j,$$
--   and let $p_j\ge\mathbb P[\theta^t=j]$ for all $t\in[T]$. Then for every initial budget $B\in\mathbb N^d$, every selection of optimal solutions $X^t$ of the fluid LPs (15) and every tie-breaking rule $K$, the Fluid Bayes Selector (Algorithm 3) satisfies
--   $$\mathbb E[\mathrm{Reg}]\ \le\ r_{\max}\sum_{j\in[n]}p_j\,(c_j+\tau_j).$$
--
--   The bound is independent of $T$ and $B$: online bipartite matching with edge weights and multiple copies of each resource has constant expected regret under the Fluid Bayes Selector, for any arrival process with the quadratic-tail condition (14).
--
--   **Formalization Note** Arrival laws are arbitrary distributions on $[n]^T$; expectations are finite sums. Eq. (14) is the All-Time Deviation bound with $\mu=\|\cdot\|_1$ and $\kappa_j=(|S_j|+1)/2$. The fictitious resource $d+1$ starts with $T$ units. The policy sends the arrival to the fictitious resource when $B^t_K=0$, a case that does not occur on sequences of positive probability.
--
--   Differences from the source:
--   - encoding: Algorithm 3 matches $\theta^t$ to $K$ with no feasibility test → Lean: match to $K$ if $B^t_K\ge1$, otherwise to the fictitious resource; reason: on every arrival sequence of positive probability $\mathbb E[Z_j(t)]>0$, hence $X^t_{Kj}\ge\mathbb E[Z_j(t)]/(d+1)>0$ and $B^t_K\ge X^t_{Kj}>0$, so the branch never changes the expected regret; it only avoids an ill-defined action on null sequences.
--   - reading: $r_{\max}$ for matching → Lean: $\max_{i,j}r_{ij}a_{ij}$; reason: $r_{\max}$ is the largest reward of an allocation; in matching the bundles are $\{i\}$ with $a_{ij}=1$ and reward $r_{ij}$ (p. 6), and the fictitious resource earns $0$.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 24, Theorem 4 (with Eq. (14), p. 24; Eq. (15), p. 24; Algorithm 3, p. 25)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals
import Definitions.Def_BayesProphet_MultiSec_Supplement_Matching

namespace BayesProphet.MultiSec.Supplement

theorem matching_regret {d n : ℕ} [NeZero n] (adj : Fin d → Fin n → Bool)
    (r : Fin d → Fin n → ℝ) (hr : ∀ i j, 0 ≤ r i j) (T : ℕ) (w : (Fin T → Fin n) → ℝ)
    (hw : IsArrivalLaw w) (c : Fin n → ℝ) (τ : Fin n → ℕ) (p : Fin n → ℝ)
    (hdev : AllTimeDeviation w l1norm (fun j => ((degree adj j : ℝ) + 1) / 2) c τ)
    (hp : ∀ j, ∀ t ∈ Finset.Icc 1 T, probL w (fun θ => θ t = j) ≤ p j)
    (B : Fin d → ℕ) (X : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → Fin n → ℝ)
    (hX : IsMatchingFluidSelection adj r w X) (K : ℕ → (Fin (d + 1) → ℕ) → Fin n → Fin (d + 1))
    (hK : IsArgmaxSelection X K) :
    matchingExpectedRegret adj r w K B ≤ matchRmax adj r * ∑ j, p j * (c j + τ j) := by sorry

end BayesProphet.MultiSec.Supplement
