-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalTriplet_one_step_stationary
-- name    : ArapostathisAC.CanonicalTriplet.one_step_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:18:06.679049+00:00
-- url     : https://prove2.me/theorems/df05efa0-c74a-4a5e-ad47-1cce31ec5386
-- title:
--   Proof of Theorem 6.2, (6.8) — one-step decomposition of $J_{N+1}(x,f,h)$ under a stationary policy
-- statement:
--   Let $(\mathbf S,\mathbf A,U,P,c)$ be a controlled Markov process with Borel state and action spaces and a cost $c\ge0$ that is bounded on $\mathbf K$. Let $f\in\Pi_{SD}$ be a stationary deterministic policy and $h\in\mathcal M_b(\mathbf S)$ a bounded measurable terminal cost. Then for every $N\in\mathbb N_0$ and every $x\in\mathbf S$,
--   $$J_{N+1}(x,f,h)=c\big(x,f(x)\big)+\int_{\mathbf S}J_N(y,f,h)\,P\big(dy\mid x,f(x)\big).$$
--
--   This is the last equality of display (6.8) in the proof of Theorem 6.2, where it is applied to $f=\pi^*$; it is also the step "$J_N(x,\pi^*,h)=c(x,\pi^*(x))+\int J_{N-1}(y,\pi^*,h)P(dy\mid x,\pi^*(x))$" of the sufficiency part. It expresses the Markov property of the controlled chain under a stationary policy.
--
--   **Formalization Note.** The paper writes (6.8) with $J^*_N$ in place of $J_N(\cdot,f,h)$, which coincide when $(\rho,h,f)$ is canonical; this item states the identity for $J_N(\cdot,f,h)$ itself, for every stationary $f$. $J_N$ is a Bochner integral with respect to the Ionescu-Tulcea path measure.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 317, proof of Theorem 6.2, (6.8) third line, and the second line of the display after "On the other hand"

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP

open MeasureTheory ProbabilityTheory

namespace ArapostathisAC.CanonicalTriplet

theorem one_step_stationary {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (f : StationaryPolicy M)
    (h : S → ℝ) (hh : IsBoundedMeas h) (N : ℕ) (x : S) :
    JN M f.toPolicy (N + 1) h x =
      M.c (x, f.1 x) + ∫ y, JN M f.toPolicy N h y ∂(M.P (x, f.1 x)) := by sorry

end ArapostathisAC.CanonicalTriplet
