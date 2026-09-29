-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed
-- name    : CerednikDrinfeld.Omega.exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/346411f5-0304-5dc3-8393-2c9723e5e7b1
-- title:
--   Equality loci of |p| and |q| are finite unions of disc conditions
-- statement:
--   Let $K$ be a field equipped with a valuation $v =$ `Valued.v` taking values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is algebraically closed; let $p, q \in K[X]$ be polynomials. The assertion is that there exist a natural number $m$ and two families $L, M : \mathrm{Fin}\,m \to$ finite sets of pairs $(e,r) \in K \times K$ such that: for every index $k$, every pair in $L\,k$ and every pair in $M\,k$ has second coordinate nonzero (the radii are nonzero); and for every $u \in K$ with $q(u) \neq 0$ one has $v(p(u)) = v(q(u))$ if and only if there is an index $k$ with $v(r) \le v(u-e)$ for all $(e,r) \in L\,k$ and $v(u-e) \le v(r)$ for all $(e,r) \in M\,k$. Thus the locus in $K \setminus q^{-1}(0)$ where the two valuations agree is cut out by finitely many alternatives, each alternative being a finite conjunction of conditions placing $u$ outside an open disc of centre $e$ and radius $|r| \ne 0$, or inside a closed disc of centre $e$ and radius $|r| \ne 0$. No nondegeneracy is assumed of $p$ or $q$, and $m = 0$ (an empty disjunction, describing the empty locus) is permitted.
--
--   This is the elementary description of the level set $\{|p| = |q|\}$ of a rational function on the affine line over an algebraically closed non-archimedean field as a finite union of affinoid "linear pieces", i.e. finite intersections of closed discs and complements of open discs. It is used in the construction of the explicit charts for the Čerednik–Drinfel'd rigid-analytic uniformisation, where it feeds [`CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.exists_linearPieces_iff_v_eval_eq_v_eval_of_isAlgClosed
    (K : Type) [Field K] [DecidableEq K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (p q : Polynomial K) :
    ∃ (m : ℕ) (L M : Fin m → Finset (K × K)),
      (∀ k, ∀ er ∈ L k, er.2 ≠ 0) ∧ (∀ k, ∀ er ∈ M k, er.2 ≠ 0) ∧
      ∀ u : K, q.eval u ≠ 0 →
        (Valued.v (p.eval u) = Valued.v (q.eval u) ↔
          ∃ k, (∀ er ∈ L k, Valued.v er.2 ≤ Valued.v (u - er.1)) ∧ (∀ er ∈ M k, Valued.v (u - er.1) ≤ Valued.v er.2)) := by sorry
