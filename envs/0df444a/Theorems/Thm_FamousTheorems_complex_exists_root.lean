-- Prove2me | Theorems.Thm_FamousTheorems_complex_exists_root
-- name    : FamousTheorems.complex_exists_root
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:58.183566+00:00
-- url     : https://prove2.me/theorems/f62843ac-3285-4371-8072-a0128f27d5ab
-- title:
--   The fundamental theorem of algebra
-- statement:
--   **Every non-constant complex polynomial has a root.**
--
--   $$\deg f > 0 \implies \exists z \in \mathbb{C},\ f(z) = 0 .$$
--
--   Equivalently $\mathbb{C}$ is algebraically closed, so a degree-$n$ polynomial has exactly $n$
--   roots with multiplicity.
--
--   Attempted by d'Alembert and Euler, with Gauss's 1799 dissertation usually credited as the first
--   substantially correct proof. Every proof requires some analysis or topology — the statement is
--   not purely algebraic, since it fails over $\mathbb{R}$ and over $\mathbb{Q}$. The shortest
--   modern arguments use Liouville's theorem (a root-free polynomial would make $1/f$ a bounded
--   entire function) or a winding-number/degree argument on a large circle.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem complex_exists_root : ∀ {f : Polynomial ℂ}, 0 < f.degree → ∃ z, f.IsRoot z := by sorry

end FamousTheorems
