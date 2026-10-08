-- Prove2me | Theorems.Thm_AronszajnRK_Operators_kernel_double_series
-- name    : AronszajnRK.Operators.kernel_double_series
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:12:51.149238+00:00
-- url     : https://prove2.me/theorems/4211943c-7110-445e-9478-cc16ee726d1e
-- title:
--   §11, Theorem III — double-series expansion of the kernel of a bounded operator
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with reproducing kernel $K$, let $\{g'_m\}$ and $\{g''_n\}$ be two complete orthonormal systems in $F$, and let $L$ be a bounded operator on $F$ with kernel $\Lambda$. Put
--   $$
--   \alpha_{mn} = (L g'_m, g''_n),
--   $$
--   the scalar product in $F$, which equals $(g''_n(y), (g'_m(x), \Lambda(x, y))_x)_y$. Then for every $x, y \in E$ the double series converges in the sense
--   $$
--   \Lambda(x, y) = \lim_{p, q \to \infty} \sum_{m=1}^{p} \sum_{n=1}^{q} \alpha_{mn}\, g'_m(x)\, \overline{g''_n(y)},
--   $$
--   the limit being taken as $p$ and $q$ tend to infinity independently (in general, as the finite sets of indices summed over grow independently).
--
--   This expansion holds for every bounded operator, whether or not its kernel belongs to the direct product $F \otimes \overline{F}$ (where the series converges absolutely).
--
--   **Formalization Note.** The two systems are Mathlib `HilbertBasis ι ℂ H` and `HilbertBasis κ ℂ H` with arbitrary index types. The partial sums run over finite index sets $P \subseteq \iota$, $Q \subseteq \kappa$, and the limit is taken along `atTop ×ˢ atTop` on `Finset ι × Finset κ`, i.e. as $P$ and $Q$ grow independently. For systems indexed by $\mathbb{N}$ this implies the paper's limit over $\{1,\dots,p\} \times \{1,\dots,q\}$ as $p, q \to \infty$; the general index set also covers finite-dimensional and non-separable spaces, where the paper's sums $\sum_{m=1}^{p}$ are read over the available indices. The coefficient is `⟪L (g′ m), g″ n⟫_ℂ`, which is the paper's $(g''_n, L g'_m)$. The theorem's second sentence (kernels in $F \otimes \overline{F}$ correspond to operators of finite norm) is not part of this statement.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), pp. 374–375, §11, Theorem III (first sentence), with (10), (11), (12)

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace Topology
open ComplexConjugate Filter

namespace AronszajnRK.Operators

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §11,
Theorem III, first sentence, with (10)–(12), pp. 374–375 (PDF pp. 38–39). Let `{g′ₘ}` and
`{g″ₙ}` be two complete orthonormal systems of a complex reproducing kernel Hilbert space and
`L` a bounded operator with kernel `Λ` (§11, Eq. (1)). With the coefficients (11)
`αₘₙ = (g″ₙ, L g′ₘ)`, which is Mathlib's `⟪L g′ₘ, g″ₙ⟫_ℂ`, the double series (10) converges
for every `x, y` in the sense (12):
`Λ(x, y) = lim_{p,q→∞} ∑_{m ≤ p} ∑_{n ≤ q} αₘₙ g′ₘ(x) \overline{g″ₙ(y)}`.
The systems are indexed by arbitrary types `ι`, `κ` and the partial sums run over finite sets
of indices `P ⊆ ι`, `Q ⊆ κ`, the limit being taken as `P` and `Q` grow independently; for
systems indexed by `ℕ` this contains the paper's limit over `{1, …, p} × {1, …, q}`, and it
also covers finite-dimensional spaces. -/
theorem kernel_double_series {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] {ι κ : Type*}
    (g₁ : HilbertBasis ι ℂ H) (g₂ : HilbertBasis κ ℂ H) (L : H →L[ℂ] H) (x y : X) :
    Tendsto (fun PQ : Finset ι × Finset κ => ∑ m ∈ PQ.1, ∑ n ∈ PQ.2,
        ⟪L (g₁ m), g₂ n⟫_ℂ * (g₁ m) x * conj ((g₂ n) y))
      (atTop ×ˢ atTop) (𝓝 (opKernel L x y)) := by sorry

end AronszajnRK.Operators
