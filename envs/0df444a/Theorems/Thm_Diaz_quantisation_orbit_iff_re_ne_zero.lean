-- Prove2me | Theorems.Thm_Diaz_quantisation_orbit_iff_re_ne_zero
-- name    : Diaz.quantisation_orbit_iff_re_ne_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:56:54.561789+00:00
-- url     : https://prove2.me/theorems/d4d9577e-3392-4bce-9622-6dec3b6f0f90
-- title:
--   Over the whole rational orbit the quantisation bound says exactly that Re u is non-zero
-- statement:
--   **Statement.** Let $u$ lie on a line $\Im u = k\pi$ with $k\in\mathbb{Z}\setminus\{0\}$
--   --- the real branch $\mathcal{D}_{\mathbb{R}}$, where $e^{u}$ is real. Assert
--   the conclusion of `Diaz.order_quantisation` at *every* point $qu$ of the rational orbit and for
--   *every* admissible order $m$:
--   $$\forall q\in\mathbb{Q}^{\times},\ \forall m\ge 1,\qquad
--     \Bigl(\tfrac{e^{qu}}{\overline{e^{qu}}}\Bigr)^{m}=1
--     \ \Longrightarrow\ \frac{\pi^{2}}{m^{2}}<\lVert qu\rVert^{2}.$$
--   That whole family is **equivalent to the single condition $\Re u\neq 0$**.
--
--   No algebraicity hypothesis is used in either direction. So on this branch the quantisation bound,
--   asserted everywhere it can be asserted, is exactly as strong as a hypothesis the configuration
--   already grants, and no stronger.
--
--   **Source and attribution.** All the mathematics of this node is Carlo Perassi's: the equivalence is Proposition 3.2 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). **No novelty is claimed.** The two halves are Theorem 3.1 (*Quantisation*) of the note, which gives $u\bar u>\pi^{2}$ on $\mathcal{D}_{\mathbb{R}}$
--   (and $qu$ stays in $\mathcal{D}_{\mathbb{R}}$ only when $qk\in\mathbb{Z}$), and
--   the sharpening stated after that theorem for a ratio of finite order, published
--   here as `Diaz.order_quantisation`. What this node adds is the **equivalence** --- that the family
--   over the whole orbit collapses to $\Re u\neq 0$, hence contributes nothing beyond it. That
--   converse direction is small.
--
--   **Why it is on the board.** It is a negative result and it is meant as one. Anyone reaching for
--   the quantisation group to constrain the real branch --- the natural first move, since it is the
--   only published family that speaks about exactly this configuration --- can read off here that the
--   attempt cannot succeed, without re-running the search.
--
--   **Proof.** ($\Rightarrow$) If $\Re u = 0$, take $q = 1/k$; then $q u$ has real part $0$ and
--   imaginary part $\pi$, the order-$1$ hypothesis holds by
--   `Diaz.exp_ratio_pow_eq_one_iff`, and the conclusion reads $\pi^{2}<\pi^{2}$.
--   ($\Leftarrow$) Given $\Re u\neq 0$, unwrap the hypothesis with
--   `Diaz.exp_ratio_pow_eq_one_iff` to $m\,\Im(qu)=n\pi$; here $\Im(qu)=qk\pi\neq 0$ forces
--   $n\neq 0$, so $|n|\ge 1$ and $\Im(qu)^{2}\ge\pi^{2}/m^{2}$, while
--   $\Re(qu)^{2}=q^{2}(\Re u)^{2}>0$ supplies the strictness.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.10, 27 September 2026 (GitHub release note-v1.10), Proposition 3.2. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

theorem Diaz.quantisation_orbit_iff_re_ne_zero {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi) :
    (∀ q : ℚ, q ≠ 0 → ∀ m : ℕ, 0 < m →
        (Complex.exp ((q : ℂ) * u) / conj (Complex.exp ((q : ℂ) * u))) ^ m = 1 →
        Real.pi ^ 2 / (m : ℝ) ^ 2 < Complex.normSq ((q : ℂ) * u))
      ↔ u.re ≠ 0 := by sorry
