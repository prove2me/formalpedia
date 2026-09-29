-- Prove2me | Theorems.Thm_DeBruijnNewman_schoenberg_polya_fourier_real_zeros
-- name    : DeBruijnNewman.schoenberg_polya_fourier_real_zeros
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T16:27:25.741363+00:00
-- url     : https://prove2.me/theorems/626a294b-1b0a-43b9-aebe-aef9f7c9a57a
-- title:
--   Schoenberg's theorem: Fourier transform of a Pólya frequency function has only real zeros
-- statement:
--   Schoenberg's theorem (I. J. Schoenberg, 1947, "On totally positive functions, distributions and Fourier transforms"): the Fourier transform of a Pólya frequency function has only real zeros. Precisely: if K : ℝ → ℝ is a Pólya frequency function (the translation kernel (x,y) ↦ K(x−y) is totally positive of every order), K is integrable, and K is not identically zero, then the entire function F(z) = ∫ K(t) e^{izt} dt has no non-real zeros.
--
--   This is the analytic heart of de Bruijn's base case (N. G. de Bruijn, "The roots of trigonometric integrals", Duke Math. J. 1950). De Bruijn's proof that H_{1/2} has only real zeros factors through exactly this theorem: the hard analytic step (de Bruijn's kernel lemma, a separate node) is that the kernel defining H_{1/2} — u ↦ e^{u²/2}Φ(u) — is a Pólya frequency function; Schoenberg's theorem then turns that total positivity into real-rootedness of its Fourier transform, i.e. of H_{1/2} (DeBruijnNewman.debruijn_base_case, 9d8af170-793b-4eb3-89af-f0602096501f). Combined with forward heat-flow monotonicity (the de Bruijn–Newman ray structure), this single implication yields H_t real-rooted for every t ≥ 1/2, fixing the right endpoint Λ ≤ 1/2 for the Rodgers–Tao argument.
-- source:
--   Decomposition of DeBruijnNewman.debruijn_base_case (9d8af170-793b-4eb3-89af-f0602096501f), Prove2Me The de Bruijn-Newman Constant is Non-negative mission

import Mathlib

namespace DeBruijnNewman

/-- A function `K : ℝ → ℝ` is a Pólya frequency function if the translation
kernel `(x, y) ↦ K (x - y)` is totally positive of every order: every
finite minor formed on strictly increasing nodes is nonnegative. -/
def IsPolyaFrequency (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ),
    (∀ i j : Fin n, i < j → x i < x j) →
    (∀ i j : Fin n, i < j → y i < y j) →
    0 ≤ (Matrix.of fun i j => K (x i - y j)).det

end DeBruijnNewman

namespace DeBruijnNewman

theorem schoenberg_polya_fourier_real_zeros
    (K : ℝ → ℝ) (hK : IsPolyaFrequency K)
    (hKint : MeasureTheory.Integrable K MeasureTheory.volume)
    (hne : ∃ t : ℝ, K t ≠ 0) :
    ∀ z : ℂ,
      MeasureTheory.integral MeasureTheory.volume
        (fun t => (K t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) = 0 →
      z.im = 0 := by
  sorry

end DeBruijnNewman
