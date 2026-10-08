-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_proposition_8_1_p506_forward
-- name    : CompOT.NotHilbertian.proposition_8_1_p506_forward
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:21.774908+00:00
-- url     : https://prove2.me/theorems/54d2862b-15d9-4a5c-8597-adb20e0f7479
-- title:
--   Proposition 8.1 (p. 506), proved direction — if d is Hilbertian then d² is negative definite
-- statement:
--   Let $\mathcal Z$ be a set and $d:\mathcal Z\times\mathcal Z\to\mathbb R$. Suppose $d$ is Hilbertian: there are a real Hilbert space $\mathcal H$ and a map $\phi:\mathcal Z\to\mathcal H$ with $d(z,z')=\|\phi(z)-\phi(z')\|_{\mathcal H}$. Then $d^2$ is negative definite: it is symmetric and, for every $n$, every $z_1,\dots,z_n\in\mathcal Z$ and every $r\in\mathbb R^n$ with $\sum_ir_i=0$,
--   $$\sum_{i,j=1}^n r_ir_j\,d^2(z_i,z_j)\le0.$$
--
--   This is the direction of Proposition 8.1 that the book proves; it turns non-embeddability into a finite test: exhibiting points and a zero-sum vector with a positive quadratic form shows that $d$ is not Hilbertian.
--
--   **Formalization Note** This is the second "Proposition 8.1" of the book (the first, on p. 494, is about $\varphi$-divergences). The converse direction (Schoenberg's theorem) is only cited by the book and is not stated here. The statement holds for any real function $d$, so no metric axioms are assumed. Negative definiteness is the zero-sum form of Definition 8.3 (see the definitions item).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 8.1 and its proof, pp. 506–507 (the second Proposition 8.1 of the book)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

universe u

/-- Proposition 8.1 (p. 506; the second "Proposition 8.1" of the book), the direction proved on
p. 507: if `d` is Hilbertian (Definition 8.4) then `d²` is negative definite (Definition 8.3,
zero-sum reading). Stated for an arbitrary real function `d` (no metric axioms are needed). -/
theorem proposition_8_1_p506_forward {Z : Type u} (d : Z → Z → ℝ) (h : IsHilbertian d) :
    IsCondNegDef (fun z z' => d z z' ^ 2) := by sorry

end CompOT.NotHilbertian
