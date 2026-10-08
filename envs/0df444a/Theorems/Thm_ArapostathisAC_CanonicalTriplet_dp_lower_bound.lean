-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalTriplet_dp_lower_bound
-- name    : ArapostathisAC.CanonicalTriplet.dp_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:18:15.268611+00:00
-- url     : https://prove2.me/theorems/fce0f73c-9468-4725-8fd2-e1c1635c9cf1
-- title:
--   Proof of Theorem 6.2, (6.8) — $J_{N+1}(x,\pi,h)\ge T(J^*_N)(x)$ for every admissible policy
-- statement:
--   Let $(\mathbf S,\mathbf A,U,P,c)$ be a controlled Markov process with Borel state and action spaces and a cost $c\ge0$ that is bounded on $\mathbf K$, let $h\in\mathcal M_b(\mathbf S)$ and $N\in\mathbb N_0$. Suppose that the optimal $N$-stage cost is a bounded measurable function: $J^*_N(\cdot,h)=v$ with $v\in\mathcal M_b(\mathbf S)$. Let $w:\mathbf S\to\mathbb R$ be any lower bound of the dynamic programming map applied to $v$,
--   $$w(x)\le c(x,a)+\int_{\mathbf S}v(y)\,P(dy\mid x,a)\qquad\forall x\in\mathbf S,\ a\in U(x),$$
--   that is, $w\le T(v)$ with $T(v)(x)=\inf_{a\in U(x)}\{c(x,a)+\int_{\mathbf S}v(y)P(dy\mid x,a)\}$ (display (2.5) of the paper). Then for every admissible policy $\pi\in\Pi$ (history-dependent and randomized) and every $x\in\mathbf S$,
--   $$w(x)\le J_{N+1}(x,\pi,h).$$
--
--   With $w=T(J^*_N)$ this is the inequality $J^*_{N+1}(\cdot,h)\ge T(J^*_N)$, one half of the second equality of (6.8), which the paper uses without proof in both parts of the proof of Theorem 6.2 ("$J^*_{N+1}(x,h)=T(J^*_N)(x)$" and "$J^*_N(x,h)=T(J^*_{N-1})(x)$"). The other half, $J^*_{N+1}\le T(J^*_N)$, is not needed: where the proof uses it, a stationary policy attaining the infimum is at hand.
--
--   **Formalization Note.** For a general Borel model, $J^*_N$ need not be measurable (the paper explains on p. 288 why it works with semicontinuous models in general), so the measurability and boundedness of $J^*_N(\cdot,h)$ is a hypothesis here; in the proof of Theorem 6.2 it holds because $J^*_N(\cdot,h)=h+N\rho$. The infimum in $T$ is not formed: any pointwise lower bound $w$ is allowed, which avoids the junk value of a real infimum and is equivalent to $J_{N+1}(x,\pi,h)\ge T(v)(x)$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 317, proof of Theorem 6.2, (6.8) second line; the map T is (2.5), p. 289

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP

open MeasureTheory ProbabilityTheory

namespace ArapostathisAC.CanonicalTriplet

theorem dp_lower_bound {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (h : S → ℝ) (hh : IsBoundedMeas h) (N : ℕ)
    (v w : S → ℝ) (hv : IsBoundedMeas v) (hvJ : ∀ y, JNopt M N h y = v y)
    (hw : ∀ x, ∀ a ∈ M.U x, w x ≤ M.c (x, a) + ∫ y, v y ∂(M.P (x, a))) :
    ∀ (π : Policy M) (x : S), w x ≤ JN M π (N + 1) h x := by sorry

end ArapostathisAC.CanonicalTriplet
