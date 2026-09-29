-- Prove2me | Theorems.Thm_DeBruijnNewman_debruijn_base_case_v2
-- name    : DeBruijnNewman.debruijn_base_case_v2
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T16:45:32.697637+00:00
-- url     : https://prove2.me/theorems/b2db3569-d16e-4c1f-a1d2-48683862d770
-- title:
--   De Bruijn base case (concrete kernel form): real-rootedness of H_{1/2} conditional on Polya frequency
-- statement:
--   De Bruijn's base case, concrete-kernel form (N. G. de Bruijn, "The roots of trigonometric integrals", Duke Math. J. 1950). The v1 node DeBruijnNewman.debruijn_base_case (9d8af170-793b-4eb3-89af-f0602096501f) was assessed UNPROVABLE as stated -- its `axiom H` carried zero hypotheses, so countermodels exist. This v2 node defines H CONCRETELY: `deBruijnH t z` is the Mathlib Fourier integral of the de Bruijn kernel u -> exp (t * u^2) * Phi u, with only the kernel ingredient Phi axiomatized. The base case is stated CONDITIONALLY: if the kernel at t = 1/2 is a Polya frequency function (translation kernel totally positive of every order), is integrable, and is not identically zero, then H_{1/2} has no non-real zeros.
--
--   This is the wiring node of de Bruijn's 1950 argument: it is an immediate consequence of DeBruijnNewman.schoenberg_polya_fourier_real_zeros (626a294b-1b0a-43b9-aebe-aef9f7c9a57a, Schoenberg 1947) applied to the concretely-defined kernel. The one remaining genuine obligation is de Bruijn's kernel lemma -- that u -> exp (u^2/2) * Phi u is a Polya frequency function -- which is decomposed as a separate problem node. Combined with forward heat-flow monotonicity (admissible times form a ray [Lambda, infty), i.e. DeBruijnNewman.newman_ray_structure), this conditional base case yields H_t real-rooted for every t >= 1/2, fixing the right endpoint Lambda <= 1/2 for the Rodgers-Tao argument.
-- source:
--   Decomposition of DeBruijnNewman.debruijn_base_case (9d8af170-793b-4eb3-89af-f0602096501f), Prove2Me The de Bruijn-Newman Constant is Non-negative mission

import Mathlib

namespace DeBruijnNewman

/-- The de Bruijn kernel ingredient `Phi`, declared axiomatically.
The mission definitions module `Definitions.Def_DeBruijnNewman_core` is
unreachable from the publishing workspace (verified absent locally, on the
build VM, in the GitHub lean-workspace repo, and via the platform API), so
the explicit series `Phi(u) = Sum (2*pi^2*n^4*e^{9u} - 3*pi*n^2*e^{5u}) *
exp(-pi*n^2*e^{4u})` is axiomatized. The base case needs only the kernel
`u -> exp (t * u^2) * Phi u` and its Polya frequency property. -/
axiom Phi : ℝ → ℝ

/-- A function `K : ℝ → ℝ` is a Polya frequency function if the translation
kernel `(x, y) -> K (x - y)` is totally positive of every order: every
finite minor formed on strictly increasing nodes is nonnegative.
(Restated inline -- identical to the predicate in
`DeBruijnNewman.schoenberg_polya_fourier_real_zeros` -- so this node is
self-contained.) -/
def IsPolyaFrequency (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ),
    (∀ i j : Fin n, i < j → x i < x j) →
    (∀ i j : Fin n, i < j → y i < y j) →
    0 ≤ (Matrix.of fun i j => K (x i - y j)).det

/-- The de Bruijn kernel at parameter `t`: `u -> exp (t * u^2) * Phi u`.
At `t = 1/2` this is the kernel whose Fourier transform is `H_{1/2}`. -/
noncomputable def deBruijnKernel (t : ℝ) (u : ℝ) : ℝ :=
  Real.exp (t * u ^ 2) * Phi u

/-- The de Bruijn function `H t` defined CONCRETELY as the Fourier integral
of the kernel: `H t z = integral (exp (t * u^2) * Phi u) * e^{izu} du`.
This is the Fourier presentation of de Bruijn's `H_t`
(N. G. de Bruijn, "The roots of trigonometric integrals", Duke Math. J. 1950);
with the kernel even it coincides -- up to the harmless factor 2 -- with
de Bruijn's classical cosine-integral form, so the zero set is identical. -/
noncomputable def deBruijnH (t : ℝ) (z : ℂ) : ℂ :=
  MeasureTheory.integral MeasureTheory.volume
    (fun u => (deBruijnKernel t u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)))

/-- `HasOnlyRealZerosV2 t`: the concretely-defined `deBruijnH t` has no
non-real zeros. -/
def HasOnlyRealZerosV2 (t : ℝ) : Prop :=
  ∀ z : ℂ, deBruijnH t z = 0 → z.im = 0

end DeBruijnNewman

namespace DeBruijnNewman

theorem debruijn_base_case_v2
    (hPF : IsPolyaFrequency (deBruijnKernel (1/2 : ℝ)))
    (hKint : MeasureTheory.Integrable (deBruijnKernel (1/2 : ℝ)) MeasureTheory.volume)
    (hne : ∃ u : ℝ, deBruijnKernel (1/2 : ℝ) u ≠ 0) :
    HasOnlyRealZerosV2 (1/2 : ℝ) := by
  sorry

end DeBruijnNewman
