-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_ne_zero_of_norm_principalMellinOf_le
-- name    : ArtinPrimitiveRoots.ne_zero_of_norm_principalMellinOf_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T10:48:40.370406+00:00
-- url     : https://prove2.me/theorems/9302a29c-a9cd-4acd-93a4-ba6eb218ed9e
-- title:
--   (8.23)–(8.25) of OpenAI's Primitive roots paper — a bound f(Z) ≪ Z^{7/15 − δ} for the Mellin integral of e^{(s−5/6)²}H/L excludes zeros of L from Re s > 1 − δ
-- statement:
--   Let $L, H : \mathbb C \to \mathbb C$ and $\delta \in \mathbb R$. Suppose that
--
--   - $L$ is holomorphic on $\{\operatorname{Re} s > 1 - \delta,\ s \ne 1\}$, has no zeros on $\operatorname{Re} s > 1$, and $|L(s)^{-1}| \le B$ for some $B$ and all $s$ with $\operatorname{Re} s \ge 2$;
--   - $H$ is holomorphic and nowhere zero on $\{\operatorname{Re} s > 1 - \delta\}$, and bounded on $\operatorname{Re} s \ge 2$;
--   - for some $C$ and $Z_0$, every real $Z \ge Z_0$ has
--   $$\Bigl|\frac{1}{2\pi i}\int_{(2)} Z^{s - 8/15}e^{(s - 5/6)^2}\frac{H(s)}{L(s)}\,ds\Bigr| \le C Z^{7/15 - \delta}$$
--   (`principalMellinOf H L Z`, the integral over the line $\operatorname{Re} s = 2$).
--
--   Then $L(s) \ne 0$ for every $s \ne 1$ with $\operatorname{Re} s > 1 - \delta$.
--
--   This is the paper's completion of the Mellin argument, stated for general $H$, $L$ and $\delta$; the paper applies it with $H = \mathcal H_\eta$, $L = L^S(\cdot, \eta)$ and $\delta = 1/20000$. Moving the line to the right gives $f(Z) = O(Z^{A})$ near $0$ (8.23); the Mellin transform $\mathcal T(s) = \int_0^\infty f(Z)Z^{-(s - 8/15)}\,dZ/Z$ (8.24) is then holomorphic on $\operatorname{Re} s > 1 - \delta$, equals $e^{(s-5/6)^2}H(s)/L(s)$ on $\operatorname{Re} s = 2$ by Fourier inversion (8.25), and so a zero of $L$ would be a pole of $\mathcal T$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), pp. 59–60: “It follows that for every $A_0 > 0$, $f_\eta(Z) = O_{A_0}(Z^{A_0})$ $(0 < Z \le 1)$, (8.23) by taking $\sigma_R > A_0 + 8/15$. […] Consider $\mathcal T(s) = \int_0^\infty f_\eta(Z)Z^{-C_*(s)}\frac{dZ}{Z}$. (8.24) By Equations (8.22) and (8.23), it converges locally uniformly, and hence defines a holomorphic function, for $\operatorname{Re} s > 1 - \frac{1}{20000}$. […] Fourier inversion therefore gives $\mathcal T(2 + i\tau) = \mathscr A(2 + i\tau)$ $(\tau \in \mathbb R)$. (8.25) […] The identity theorem, first on $\operatorname{Re} s > 1$ using Equation (8.25) and then for meromorphic functions on the connected larger half-plane, identifies $\mathscr A$ with the holomorphic function $\mathcal T$. A zero of $L^S(s, \eta)$ in that half-plane would be a pole of $\mathscr A$, since its numerator is nonzero, which is impossible.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 59–60, proof of Theorem 1.2, §8.3, (8.23)–(8.25)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe

namespace ArtinPrimitiveRoots

theorem ne_zero_of_norm_principalMellinOf_le (L H : ℂ → ℂ) (δ : ℝ)
    (hL : DifferentiableOn ℂ L {s | 1 - δ < s.re ∧ s ≠ 1})
    (hL1 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B)
    (hH : DifferentiableOn ℂ H {s | 1 - δ < s.re})
    (hH0 : ∀ s : ℂ, 1 - δ < s.re → H s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ B)
    (hf : ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
      ‖principalMellinOf H L Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - δ)) :
    ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → L s ≠ 0 := by
  sorry

end ArtinPrimitiveRoots
