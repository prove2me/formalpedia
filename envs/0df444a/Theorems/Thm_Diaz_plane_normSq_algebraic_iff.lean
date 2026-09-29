-- Prove2me | Theorems.Thm_Diaz_plane_normSq_algebraic_iff
-- name    : Diaz.plane_normSq_algebraic_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:53.386375+00:00
-- url     : https://prove2.me/theorems/a6e30e32-bc9a-4100-82c9-dcc7080fdb9b
-- title:
--   In the plane spanned by a torsion-branch candidate and its conjugate only the two axes have algebraic modulus
-- statement:
--   **Statement.** Let $u$ satisfy $\Im u = k\pi$ with $k\in\mathbb{Z}\setminus\{0\}$ and let
--   $u\bar u=\lVert u\rVert^{2}$ be algebraic. Then for rationals $a,b$,
--   $$\lVert a u + b\,\bar u\rVert^{2}\in\bar{\mathbb{Q}}
--     \qquad\Longleftrightarrow\qquad a=0\ \text{ or }\ b=0 .$$
--
--   In words: inside the real plane $\mathbb{Q}u\oplus\mathbb{Q}\bar u$, the only points with
--   algebraic modulus are the rational multiples of $u$ and the rational multiples of $\bar u$. Every
--   genuine mixture leaves the locus.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's; it is unpublished apart from this node. **No novelty is claimed.** This is part **(a)** of his classification of the period
--   plane, $V_u\cap\mathcal{D}
--   =\mathbb{Q}^{\times}u\,\dot\cup\,\mathbb{Q}^{\times}\bar u$ for $\Im u\in\pi\mathbb{Q}$,
--   formalised here in the slightly smaller range $\Im u\in\pi\mathbb{Z}$. Only the unconditional
--   norm identity of that classification's proof had been published, as
--   `Diaz.period_plane_norm`; the classification it is there to serve had not. Nothing here is new.
--
--   **Proof.** The identity `Diaz.period_plane_norm` at $c=0$ gives
--   $\lVert a u + b\bar u\rVert^{2}=(a+b)^{2}\lVert u\rVert^{2}-4ab\,(\Im u)^{2}$, and
--   $(\Im u)^{2}=k^{2}\pi^{2}$. So the left-hand side differs from the algebraic number
--   $(a+b)^{2}\lVert u\rVert^{2}$ by the rational multiple $4abk^{2}$ of $\pi^{2}$. If $ab\neq 0$
--   that multiple is non-zero and algebraicity of the left-hand side would make $\pi^{2}$ algebraic,
--   against `DiazModulus.pi_sq_transcendental`; if $ab=0$ the term vanishes and what is left is
--   algebraic.

import Mathlib

open ComplexConjugate

theorem Diaz.plane_normSq_algebraic_iff {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi)
    (hn : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ)) (a b : ℚ) :
    IsAlgebraic ℚ ((Complex.normSq ((a : ℂ) * u + (b : ℂ) * conj u) : ℝ) : ℂ)
      ↔ a = 0 ∨ b = 0 := by sorry
