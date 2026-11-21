-- Prove2me | Theorems.Thm_BehrendWindows_relation_of_map_relation
-- name    : BehrendWindows.relation_of_map_relation
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:46:49.854179+00:00
-- url     : https://prove2.me/theorems/70b9543b-f4af-4301-84a2-fefba93c1f03
-- title:
--   No carries in base $md$
-- statement:
--   Let $n,d,m,p,q\in\mathbb{N}$ with $p,q\ge 1$ and $p+q<m$, and let $x,y,z\in\mathbb{N}^n$ have every entry strictly below $d$. For $w\in\mathbb{N}^n$ write
--
--   $$\phi(w)=\sum_{i<n} w_i\,(md)^i$$
--
--   for the number with base-$(md)$ digits $w_0,\dots,w_{n-1}$. If
--
--   $$p\,\phi(x)+q\,\phi(z)=(p+q)\,\phi(y),$$
--
--   then the same relation holds coordinatewise: $p\,x+q\,z=(p+q)\,y$.
--
--   Because all digits are below $d$ and $p+q<m$, both sides are base-$(md)$ expansions without carries, so the identity of numbers lifts to an identity of digit vectors. This is the arithmetic half of Behrend's construction.
--
--   **Formalization Note** $\phi$ is Mathlib's `Behrend.map (m * d)`.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, milestone 2; generalises the no-carry step of F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, PNAS 32 (1946) 331-332, https://doi.org/10.1073/pnas.32.12.331

import Mathlib

namespace BehrendWindows

theorem relation_of_map_relation {n : ℕ} (d m p q : ℕ) (x y z : Fin n → ℕ)
    (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) (hz : ∀ i, z i < d)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q < m)
    (h : p * Behrend.map (m * d) x + q * Behrend.map (m * d) z = (p + q) * Behrend.map (m * d) y) :
    p • x + q • z = (p + q) • y := by sorry

end BehrendWindows
