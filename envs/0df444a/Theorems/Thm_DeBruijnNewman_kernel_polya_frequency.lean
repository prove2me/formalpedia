-- Prove2me | Theorems.Thm_DeBruijnNewman_kernel_polya_frequency
-- name    : DeBruijnNewman.kernel_polya_frequency
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T17:13:35.451242+00:00
-- url     : https://prove2.me/theorems/9e726a1c-08bb-4108-8a6b-3998b6563706
-- title:
--   De Bruijn's kernel lemma: the kernel u -> exp(u^2/2)*Phi(u) is a Polya frequency function
-- statement:
--   De Bruijn's kernel lemma (N. G. de Bruijn, "The roots of trigonometric integrals", Duke Math. J. 1950): the de Bruijn kernel at t = 1/2 -- u -> exp (u^2/2) * Phi u -- is a Polya frequency function, i.e. its translation kernel (x, y) -> K(x - y) is totally positive of every order.
--
--   This is the hard analytic step of de Bruijn's 1950 base case. The proof of that base case factors into three independent nodes: this kernel lemma (total positivity of the kernel), DeBruijnNewman.schoenberg_polya_fourier_real_zeros (626a294b-1b0a-43b9-aebe-aef9f7c9a57a, Schoenberg 1947 -- the Fourier transform of a Polya frequency function has only real zeros), and DeBruijnNewman.debruijn_base_case_v2 (b2db3569-d16e-4c1f-a1d2-48683862d770, the wiring node stating H_{1/2} real-rooted conditional on exactly the kernel's Polya frequency property). Applying Schoenberg's theorem to this kernel lemma discharges the hPF hypothesis of debruijn_base_case_v2, giving H_{1/2} with no non-real zeros; combined with forward heat-flow monotonicity (the de Bruijn-Newman ray structure) this yields H_t real-rooted for every t >= 1/2, fixing the right endpoint Lambda <= 1/2 for the Rodgers-Tao argument.
-- source:
--   Decomposition of DeBruijnNewman.debruijn_base_case_v2 (b2db3569-d16e-4c1f-a1d2-48683862d770), Prove2Me The de Bruijn-Newman Constant is Non-negative mission

import Mathlib

namespace DeBruijnNewman

/-- The de Bruijn kernel ingredient `Phi`, declared axiomatically.
The mission definitions module `Definitions.Def_DeBruijnNewman_core` is
unreachable from the publishing workspace (verified absent locally, on the
build VM, in the GitHub lean-workspace repo, and via the platform API), so
the explicit series `Phi(u) = Sum (2*pi^2*n^4*e^{9u} - 3*pi*n^2*e^{5u}) *
exp(-pi*n^2*e^{4u})` is axiomatized. This node needs only the kernel
`u -> exp (t * u^2) * Phi u` and its Polya frequency property. -/
axiom Phi : ℝ → ℝ

/-- A function `K : ℝ → ℝ` is a Polya frequency function if the translation
kernel `(x, y) -> K (x - y)` is totally positive of every order: every
finite minor formed on strictly increasing nodes is nonnegative.
(Restated inline -- identical to the predicate in
`DeBruijnNewman.schoenberg_polya_fourier_real_zeros` and
`DeBruijnNewman.debruijn_base_case_v2` -- so this node is self-contained.) -/
def IsPolyaFrequency (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ),
    (∀ i j : Fin n, i < j → x i < x j) →
    (∀ i j : Fin n, i < j → y i < y j) →
    0 ≤ (Matrix.of fun i j => K (x i - y j)).det

/-- The de Bruijn kernel at parameter `t`: `u -> exp (t * u^2) * Phi u`.
At `t = 1/2` this is the kernel whose Fourier transform is `H_{1/2}`.
(Identical to the kernel in `DeBruijnNewman.debruijn_base_case_v2` -- the
`hPF` hypothesis there is literally this lemma's conclusion.) -/
noncomputable def deBruijnKernel (t : ℝ) (u : ℝ) : ℝ :=
  Real.exp (t * u ^ 2) * Phi u

end DeBruijnNewman

namespace DeBruijnNewman

theorem kernel_polya_frequency :
    IsPolyaFrequency (deBruijnKernel (1/2 : ℝ)) := by
  sorry

end DeBruijnNewman
