-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lc_barrier_positive
-- name    : BirkhoffGlobalSection.lc_barrier_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-26T17:01:23.790117+00:00
-- url     : https://prove2.me/theorems/50b3ee92-b602-4020-b83a-b8e7168a832f
-- title:
--   The circle $|q+\mu|=(3-2\mu)/5$ lies outside Hill's region (Levi-Civita form)
-- statement:
--   We work in the planar circular restricted three-body problem in rotating coordinates. The primary of mass $1-\mu$ sits at $(-\mu,0)$ and the primary of mass $\mu$ at $(1-\mu,0)$, and we fix the Jacobi energy level $H=-c$. The Levi-Civita regularization at the first primary uses complex coordinates $z=z_1+iz_2$ and $w=w_1+iw_2$ with $q+\mu=2z^2$ and $p=w/\bar z$. In these coordinates the regularized Hamiltonian of Joung–van Koert (eq. (4.1)) reads
--
--   $$
--   K_{\mu,c}(z,w)=\tfrac12\,\lvert w+A(z)z\rvert^2+z^{\mathsf T}B(z)\,z-\frac{1-\mu}{2},
--   $$
--
--   where, with $r=\lvert 2z^2-1\rvert=\sqrt{(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2}$ the distance to the second primary,
--
--   $$
--   B(z)=\begin{pmatrix} c-\tfrac12(2\lvert z\rvert^2-\mu)^2-\dfrac{\mu}{r} & 0\\[4pt] 0 & c-\tfrac12(2\lvert z\rvert^2+\mu)^2-\dfrac{\mu}{r}\end{pmatrix}.
--   $$
--
--   **Statement.** Let $0\le\mu\le\tfrac12$ and $c\ge\tfrac{21}{10}$. Let $z=(z_1,z_2)\in\mathbb R^2$ lie on the circle
--
--   $$
--   2\,(z_1^2+z_2^2)=\frac{3-2\mu}{5},
--   $$
--
--   which is the Levi-Civita lift of the circle $\lvert q+\mu\rvert=\frac{3-2\mu}{5}$ around the first primary. Let $r>0$ satisfy $r^2=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$. Then
--
--   $$
--   \Big(c-\tfrac12\big(2\lvert z\rvert^2-\mu\big)^2-\frac{\mu}{r}\Big)z_1^2+\Big(c-\tfrac12\big(2\lvert z\rvert^2+\mu\big)^2-\frac{\mu}{r}\Big)z_2^2\;>\;\frac{1-\mu}{2},
--   $$
--
--   that is, $z^{\mathsf T}B(z)\,z>\frac{1-\mu}{2}$.
--
--   Since $K_{\mu,c}(z,w)\ge z^{\mathsf T}B(z)z-\frac{1-\mu}{2}$ for every $w$, the inequality says that $K_{\mu,c}>0$ over the whole circle and for all momenta. Equivalently, the circle $\lvert q+\mu\rvert=\frac{3-2\mu}{5}$ lies outside Hill's region.
--
--   **Relation to the sources.** This is the all-angle form of Lemma 4.1 of Joung–van Koert. Lemma 4.1 bounds the distance $d_{\mu,c}$ from $(-\mu,0)$ to the boundary of Hill's region along the axis between the primaries by $\frac{3-2\mu}{5}$. For the other directions it relies on the fact that this distance is maximal on that axis. That fact is Lemma 5.2 and Corollary 5.3 of Albers–Frauenfelder–van Koert–Paternain (*The contact geometry of the restricted 3-body problem*, Comm. Pure Appl. Math. 2012, arXiv:1010.2140): on every circle of radius $\rho<1$ around a primary, the effective potential is smallest in the direction of the first Lagrange point. The two lemmas together give the statement here, so it is not a new result. What this node adds is a single self-contained statement in Levi-Civita coordinates, with a purely algebraic proof that does not minimize over the angle. It is the containment $2\lvert z\rvert^2<\frac{3-2\mu}{5}$ that the computer-assisted proof of Proposition 4.4 (positive tangential Hessian) uses to discard boxes.
--
--   **Formalization Note.** The distance $r=\lvert 2z^2-1\rvert$ is a real variable constrained by $r>0$ and $r^2=\lvert 2z^2-1\rvert^2$, so the statement is pure real arithmetic. No upper bound on $c$ is needed.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Section 4: Lemma 4.1 (bound d_{mu,c} <= (3-2mu)/5, proved there on the collinear axis) extended to the whole circle |q+mu| = (3-2mu)/5, which also follows from Albers–Frauenfelder–van Koert–Paternain, The contact geometry of the restricted 3-body problem, CPAM 2012, https://arxiv.org/abs/1010.2140, Lemma 5.2 and Corollary 5.3; B(z) as in eq. (4.1); used for the box test 2|z|^2 > (3-2mu)/5 in the proof of Proposition 4.4.

import Mathlib.Data.Real.Basic

namespace BirkhoffGlobalSection

/-- The circle `2|z|² = (3 - 2μ)/5` (i.e. `|q + μ| = (3 - 2μ)/5`) lies outside the Hill region
in Levi-Civita coordinates: `zᵀ B(z) z > (1 - μ)/2` there, with `r = |2z² - 1|`. -/
theorem lc_barrier_positive (μ c z₁ z₂ r : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc0 : 21 / 10 ≤ c)
    (hz : 2 * (z₁ ^ 2 + z₂ ^ 2) = (3 - 2 * μ) / 5)
    (hr : 0 < r) (hr2 : r ^ 2 = (2 * (z₁ ^ 2 - z₂ ^ 2) - 1) ^ 2 + (4 * z₁ * z₂) ^ 2) :
    (1 - μ) / 2 <
      (c - (2 * (z₁ ^ 2 + z₂ ^ 2) - μ) ^ 2 / 2 - μ / r) * z₁ ^ 2
        + (c - (2 * (z₁ ^ 2 + z₂ ^ 2) + μ) ^ 2 / 2 - μ / r) * z₂ ^ 2 := by sorry

end BirkhoffGlobalSection
