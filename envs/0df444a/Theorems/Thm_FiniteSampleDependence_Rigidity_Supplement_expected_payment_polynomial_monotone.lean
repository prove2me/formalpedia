-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_expected_payment_polynomial_monotone
-- name    : FiniteSampleDependence.Rigidity.Supplement.expected_payment_polynomial_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:51:10.116836+00:00
-- url     : https://prove2.me/theorems/51e51f99-6b60-4ba7-a9fe-f140e8c9944e
-- title:
--   Lemma 6.1 — independence-zero, Alice-truthful payments have polynomial (LF-DPI), (IZ) expected payments of degree $\le\ell$
-- statement:
--   Let $n,m\ge2$ and $\ell\in\mathbb N$, and let $M_A:([n]\times[m])^\ell\to\mathbb R$ be Alice's payment in the peer-prediction model of §6. Suppose
--
--   1. $M_A$ is independence-zero: $\mathbb E_{U^{\otimes\ell}}[M_A]=0$ for every rank-one $U\in\Delta_{n,m}$;
--   2. Alice cannot gain by any memoryless deviation when Bob is truthful, for any $P$: $\mathbb E_{(TP)^{\otimes\ell}}[M_A]\le\mathbb E_{P^{\otimes\ell}}[M_A]$ for every $P\in\Delta_{n,m}$ and every column-stochastic $T\in\mathbb R^{n\times n}$.
--
--   Then the expected payment
--   $$F_A(U)=\mathbb E_{U^{\otimes\ell}}[M_A]=\sum_{((x_t,y_t))_{t=1}^\ell}M_A\big((x_t,y_t)_{t=1}^\ell\big)\prod_{t=1}^\ell U_{x_ty_t}$$
--   is represented on $\Delta_{n,m}$ by a real polynomial $Q$ in the entries $U_{i\alpha}$ of total degree at most $\ell$ whose functional $U\mapsto Q(U)$ satisfies (LF-DPI) and (IZ).
--
--   The lemma turns incentive conditions on a multi-task mechanism into the algebraic hypotheses of the mission's goal (Theorem B) and of tall-case collapse.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: the i.i.d. expectation E_{V^{⊗ℓ}}[M] of a payment rule → the exact finite sum Σ_{z ∈ ([n]×[m])^ℓ} M(z) ∏_t V_{x_t y_t} (expectedPayment), the paper's equation (6); reason: for finitely many outcomes the expectation is this sum; no measure-theoretic model is introduced
--   - encoding: F_A is represented by a polynomial of degree at most ℓ satisfying (LF-DPI) and (IZ) → some Q : PolyRing n m with totalDegree ≤ ℓ, polyFun Q = expectedPayment M_A on Δ_{n,m}, and LFDPI (polyFun Q) ∧ IZ (polyFun Q); reason: (LF-DPI) and (IZ) read a functional only on Δ_{n,m} (TU stays in Δ_{n,m}), where polyFun Q and F_A agree, so the conditions on the representative are the conditions on F_A
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Lemma 6.1, PDF p. 17 (printed p. 16); model of §6, same page; eq. (6)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Lemma 6.1 (Expected payments are polynomial monotones), PDF p. 17 (printed p. 16). If Alice's
`ℓ`-task payment `M_A` is independence-zero and she cannot gain by any memoryless deviation when
Bob is truthful, for any `P`, then `F_A(U) = E_{U^{⊗ℓ}}[M_A]` is represented on `Δ_{n,m}` by a
polynomial of degree at most `ℓ` satisfying (LF-DPI) and (IZ). -/
theorem expected_payment_polynomial_monotone {n m ℓ : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (MA : (Fin ℓ → Fin n × Fin m) → ℝ) (hIZ : PaymentIZ MA) (hA : AliceTruthful MA) :
    ∃ Q : PolyRing n m, Q.totalDegree ≤ ℓ ∧
      (∀ U ∈ simplex n m, polyFun Q U = expectedPayment MA U) ∧
      LFDPI (polyFun Q) ∧ IZ (polyFun Q) := by sorry

end FiniteSampleDependence.Rigidity.Supplement
