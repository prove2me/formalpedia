-- Prove2me | Theorems.Thm_ChatterjeeQFT_massShell_eq_graph
-- name    : ChatterjeeQFT.massShell_eq_graph
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:15:48.30373+00:00
-- url     : https://prove2.me/theorems/dd4e4359-f85b-4d79-8cdf-9f7e53c3b66e
-- title:
--   The mass shell is the graph of the energy function $q \mapsto (\omega_q, q)$
-- statement:
--   For every real $m$ and every four-vector $p$, the two following statements are
--   equivalent:
--
--   $$p \in X_m \;=\; \{p : p^2 = m^2,\ p^0 \ge 0\}
--   \qquad\Longleftrightarrow\qquad
--   p = (\omega_q, q) \ \text{ for some } q \in \mathbb{R}^3,$$
--
--   where $\omega_q = \sqrt{m^2 + |q|^2}$. In words: a four-momentum lies on the mass shell exactly
--   when its spatial part $q$ is arbitrary and its energy is the relativistic energy $\omega_q$ of
--   that spatial part. This is the statement that the map $q \mapsto (\omega_q, q)$ of Lecture 10 is
--   a parametrisation of $X_m$ by $\mathbb{R}^3$, which is what makes the integration formula (10.1)
--   meaningful.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 9 §9.5, p. 40 (definition of the mass shell $X_m$ and the relation $p^0 = \omega_{\mathbf p}$).

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem massShell_eq_graph (m : ℝ) (p : Fin 4 → ℝ) :
    p ∈ massShell m ↔ ∃ q : Fin 3 → ℝ, p = massShellEmb m q := by sorry

end ChatterjeeQFT
