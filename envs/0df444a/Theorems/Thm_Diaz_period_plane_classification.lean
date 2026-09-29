-- Prove2me | Theorems.Thm_Diaz_period_plane_classification
-- name    : Diaz.period_plane_classification
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:53.857675+00:00
-- url     : https://prove2.me/theorems/825f3b6f-f994-4d8c-9730-58454a8bed78
-- title:
--   Adding the period to a point of the period plane returns to the locus only in two cases
-- statement:
--   **Statement.** Let $\Im u = k\pi$ with $k\in\mathbb{Z}\setminus\{0\}$ and
--   $\lVert u\rVert^{2}\in\bar{\mathbb{Q}}$. For rationals $a,b,c$,
--   $$\lVert a u + b\,\bar u + 2\pi c\, i\rVert^{2}\in\bar{\mathbb{Q}}
--     \qquad\Longleftrightarrow\qquad c=-ak\ \text{ or }\ c=bk .$$
--
--   In the first case the point equals $(a+b)\bar u$, in the second $(a+b)u$. So on this branch the
--   period $2\pi i$ contributes nothing new: adding any rational multiple of it to any point of the
--   plane $\mathbb{Q}u\oplus\mathbb{Q}\bar u$ lands back on the locus only when the result is
--   already a rational multiple of $u$ or of $\bar u$.
--
--   The reason this covers the whole space $V_u=\mathbb{Q}u+\mathbb{Q}\bar u+\mathbb{Q}\,2\pi i$
--   at once is that here $2\pi i=(u-\bar u)/k$ already lies in the plane spanned by $u$ and $\bar u$
--   --- which is exactly what fails off the torsion branch.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's; it is unpublished apart from this node. **No novelty is claimed.** This is part **(a)** of his classification of the period
--   plane --- $V_u=\mathbb{Q}u\oplus\mathbb{Q}\bar u$ and
--   $V_u\cap\mathcal{D}=\mathbb{Q}^{\times}u\,\dot\cup\,\mathbb{Q}^{\times}\bar u$ when
--   $\Im u\in\pi\mathbb{Q}$ --- formalised in the range $\Im u\in\pi\mathbb{Z}$ and in the
--   coordinates $(a,b,c)$ of that classification's own proof. Of that classification only the norm identity
--   had been published, as `Diaz.period_plane_norm`. Nothing here is new.
--
--   **Proof.** Since $u-\bar u=2ik\pi$, the point $a u + b\bar u + 2\pi ci$ equals
--   $(a+c/k)\,u+(b-c/k)\,\bar u$. Apply `Diaz.plane_normSq_algebraic_iff` to that pair of
--   coefficients: the modulus is algebraic exactly when $a+c/k=0$ or $b-c/k=0$, that is $c=-ak$ or
--   $c=bk$.

import Mathlib

open ComplexConjugate

theorem Diaz.period_plane_classification {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi)
    (hn : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ)) (a b c : ℚ) :
    IsAlgebraic ℚ ((Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u
        + 2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) : ℝ) : ℂ)
      ↔ (c = -(a * (k : ℚ)) ∨ c = b * (k : ℚ)) := by sorry
