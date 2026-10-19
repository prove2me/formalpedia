-- Prove2me | Theorems.Thm_FlatlyFoliated_compact_poisson_potential_three
-- name    : FlatlyFoliated.compact_poisson_potential_three
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T19:36:51.86044+00:00
-- url     : https://prove2.me/theorems/371bd1b1-d05d-4aff-9042-bdacc65518de
-- title:
--   Smooth compact-source Poisson potential with global derivative decay in three dimensions
-- statement:
--   Let $q:\mathbb R^3\to\mathbb R$ be smooth and compactly supported. There is a smooth function $h:\mathbb R^3\to\mathbb R$ and a constant $C>0$ such that
--
--   $$\Delta h=q$$
--
--   and, for every $x\in\mathbb R^3$,
--
--   $$|h(x)|\le\frac{C}{1+|x|},\qquad
--   \|Dh(x)\|\le\frac{C}{(1+|x|)^2},\qquad
--   \|D^2h(x)\|\le\frac{C}{(1+|x|)^3}.$$
--
--   These are global bounds, including the source region and the origin. The derivatives carry their Euclidean operator norms. No sign or zero-integral hypothesis is imposed on the source. Such estimates control compact-source corrections in decompositions of exterior radial vector fields and in elliptic boundary conditions at infinity.
--
--   **Formalization Note** The Laplacian is the sum of three pure coordinate second derivatives. The Hessian norm is the operator norm of the derivative of the continuous-linear-map-valued first derivative.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, Chapter 2, Sections 2.6–2.7.1, printed pp. 33–37, Theorems 2.25–2.26 and equations (2.12), (2.14), (2.16), (2.24)–(2.25): the three-dimensional Newtonian potential of a smooth compactly supported source, with the zeroth, first and second differentiated-kernel far-field bounds extended over the compact source region by smoothness. https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf . Applied in Bray–Hamm–Hirsch–Wheeler–Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, proof of Corollary 2, equations (101)–(102). https://arxiv.org/html/1911.00967v2

import Definitions.Def_FlatlyFoliatedRelativity_basic
open scoped ContDiff Topology
open FlatlyFoliated Filter

theorem FlatlyFoliated.compact_poisson_potential_three
    (q : R3 → ℝ) (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) :
    ∃ h : R3 → ℝ, ContDiff ℝ ∞ h ∧ (∀ x, lap h x = q x) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x : R3,
        |h x| ≤ C / (1 + ‖x‖) ∧
        ‖fderiv ℝ h x‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C / (1 + ‖x‖) ^ 3 := by sorry
