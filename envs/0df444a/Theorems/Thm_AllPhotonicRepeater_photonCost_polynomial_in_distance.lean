-- Prove2me | Theorems.Thm_AllPhotonicRepeater_photonCost_polynomial_in_distance
-- name    : AllPhotonicRepeater.photonCost_polynomial_in_distance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:49.940886+00:00
-- url     : https://prove2.me/theorems/53d4b230-4fff-46af-b866-9d36ad329ce6
-- title:
--   App. C1, conclusion after (C12): $\bar Q$ scales polynomially with the distance for every $\epsilon_0<1/2$
-- statement:
--   Let $0\le\epsilon_0<1/2$ be the per-photon loss probability. There are a constant $C$ and a degree $k\in\mathbb N$, depending on $\epsilon_0$ only, such that for every number $n$ of source nodes the free parameters of the protocol can be chosen — $m\ge1$ arms per side of each cluster state and a tree cluster state with depth index $l\ge1$ and branching $b_i\ge1$ for $i\le l$ — so that the success probability (C1) is positive and the average number (C4) of single photons per entangled pair satisfies
--   $$
--   \bar Q=\frac{2mn(Q_L+1)+2m}{P}\le C\,(n+1)^k .
--   $$
--   Since Alice and Bob are $L=(n+1)L_0$ apart, for a fixed spacing $L_0$ this says $\bar Q\le (C/L_0^{k})\,L^k$: the photon cost of the all photonic repeater grows only polynomially with the distance, whereas direct transmission needs exponentially many photons.
--
--   The paper reaches this conclusion through the upper bound (C9), the approximate parameter choice (C10)–(C11) and the numerical fit (A4); this item states the conclusion itself.
--
--   Differences from the source:
--   - reading: $\epsilon_0$ "selected to satisfy $\epsilon_0<0.5$" (p. 11) → $\epsilon_0$ a fixed real with $0\le\epsilon_0<1/2$, independent of $n$, $m$ and the tree; reason: the scaling argument on p. 12 treats $\epsilon_0$ as a constant ("we can choose any $x>0$ as long as $\epsilon_0<0.5$"); (C6) is a physical estimate, not part of the model
--   - reading: (A3) printed for $1\le k\le l$ → $R_k$ given by (A3) also at $k=0$; reason: (A16) reads $P_X=R_0$, and (A7), (A9), (A12) give $R_k=1-(1-S_k)^{b_k}$ at every level, $k=0$ included
--   - encoding: $R_{l+1}:=0$ and $b_{l+1}:=0$ → $R_k=0$ and $b_k$ read as $0$ for every $k>l$; reason: $R_{l+2}$ enters only $R_l$, raised to the power $b_{l+1}=0$, so its value never matters; same instances
--   - reading: "choose all the parameters so as to minimize $\bar Q$" (p. 11) → existential over $m\ge1$, $l\ge1$, $b_0,\dots,b_l\ge1$, asserting $P>0$; reason: a bound on the minimum is a bound for some admissible choice; $P>0$ excludes Lean's $x/0=0$
--   - encoding: distance $L$, with $n=L/L_0-1$ → $n+1$; reason: for a fixed $L_0$, $\bar Q\le C(n+1)^k$ iff $\bar Q\le (C/L_0^k)L^k$
--   - reading: "scales only polynomially with distance $L$" → $\exists C,k$ (depending on $\epsilon_0$ only), $\forall n$, $\bar Q\le C(n+1)^k$; reason: standard meaning; the paper's (C12) also depends on $\epsilon_0$ through $P_B$ and $x$
--   - encoding: exponent $2(m-1)n$ → natural-number exponent `2 * (m - 1) * n` with truncated subtraction; reason: differs only at $m=0$, which the statement excludes ($m\ge1$)
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. C1, conclusion after Eq. (C12), p. 12; Eqs. (C1), (C2), (C4), p. 11; abstract, p. 1

import Mathlib
import Definitions.Def_AllPhotonicRepeater_expectedPhotons

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. C1, conclusion
after Eq. (C12), p. 12 (also the abstract, p. 1, and §V, p. 5): "Since `n = L/L0 − 1`, it is
concluded that the average number `Q̄` of the total single photons required to produce an
entangled pair scales only polynomially with distance `L`."

For every per-photon loss probability `0 ≤ ε0 < 1/2` there are a constant `C` and a degree `k`
such that for every number `n` of source nodes some choice of the free parameters — `m ≥ 1`
arms per side, a tree of depth index `l ≥ 1` with branching `b_i ≥ 1` for `i ≤ l` — gives a
positive success probability `P` (C1) and an average photon number (C4)
`Q̄ ≤ C (n + 1)^k`.

**Formalization Note** Quantifier order: `∀ ε0, ∃ C k, ∀ n, ∃ m l b`; `C` and `k` depend on
`ε0` only. The distance is `L = (n + 1) L_0`; for a fixed spacing `L_0`,
`Q̄ ≤ C (n + 1)^k` is the same as `Q̄ ≤ (C / L_0^k) L^k`. The parameters are existential because
the page chooses them "so as to minimize `Q̄`" (p. 11). `0 < P` is asserted because `Q̄` is a
real division, which Lean evaluates to `0` at `P = 0`. `ε0` is a fixed model parameter; the
physical estimate (C6) is not part of the model. -/
theorem photonCost_polynomial_in_distance (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 < 1 / 2) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, ∃ m l : ℕ, ∃ b : ℕ → ℕ,
      1 ≤ m ∧ 1 ≤ l ∧ (∀ i ≤ l, 1 ≤ b i) ∧
      0 < repeaterSuccess ε0 n m l b ∧
      expectedPhotons ε0 n m l b ≤ C * ((n : ℝ) + 1) ^ k := by sorry

end AllPhotonicRepeater
