-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_linear_extension_of_bilinear_extension
-- name    : BilinearMapExtension.Complemented.linear_extension_of_bilinear_extension
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:51.690983+00:00
-- url     : https://prove2.me/theorems/f4a7df90-ccdf-48af-9cc9-8f5d6ac502ab
-- title:
--   §5, proof of Theorem 5.2, (a1)⇒(a2), p. 5 — if every bounded bilinear map on M×N extends, every bounded operator on M (on N) extends to X (to Y)
-- statement:
--   Let $\mathcal M$ and $\mathcal N$ be linear manifolds of normed spaces $\mathcal X$ and $\mathcal Y$ over $\mathbb F\in\{\mathbb R,\mathbb C\}$, and let $\mathcal Z$ be a normed space. Suppose every bounded bilinear map $\phi\in\boldsymbol b[\mathcal M\times\mathcal N,\mathcal Z]$ has a bounded bilinear extension $\widehat\phi\in\boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z]$, $\widehat\phi|_{\mathcal M\times\mathcal N}=\phi$. Then:
--
--   1. if $\mathcal N \ne \{0\}$, every $T\in\mathcal B[\mathcal M,\mathcal Z]$ has an extension $\widehat T\in\mathcal B[\mathcal X,\mathcal Z]$ with $\widehat T|_{\mathcal M} = T$;
--   2. if $\mathcal M \ne \{0\}$, every $S\in\mathcal B[\mathcal N,\mathcal Z]$ has an extension $\widehat S\in\mathcal B[\mathcal Y,\mathcal Z]$ with $\widehat S|_{\mathcal N} = S$.
--
--   $$\bigl(\forall\phi\ \exists\widehat\phi:\ \widehat\phi|_{\mathcal M\times\mathcal N}=\phi\bigr) \;\Longrightarrow\; \bigl(\forall T\ \exists\widehat T:\ \widehat T|_{\mathcal M}=T\bigr) \text{ when } \mathcal N\ne\{0\}.$$
--
--   This is the first step of the necessity direction of Theorem 5.2(a): the bilinear extension property passes to a linear extension property on each factor.
--
--   **Formalization Note.** The hypotheses $\mathcal N\ne\{0\}$ and $\mathcal M\ne\{0\}$ come from the opening line of the paper's proof ("Let $\mathcal M$ and $\mathcal N$ be nonzero linear manifolds"); each half needs only the nonvanishing of the *other* factor. Completeness of $\mathcal X,\mathcal Y,\mathcal Z$ is not needed for this step, and $\mathcal Z$ is fixed.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 5, §5, proof of Theorem 5.2, (a1)⇒(a2)

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented

/-- §5, proof of Theorem 5.2, (a1)⇒(a2), p. 5. -/
theorem linear_extension_of_bilinear_extension {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y)
    (h : ∀ φ : M →L[𝕜] N →L[𝕜] Z, ∃ φh : X →L[𝕜] Y →L[𝕜] Z, IsBilinExtension M N φ φh) :
    (N ≠ ⊥ → ∀ T : M →L[𝕜] Z, ∃ Th : X →L[𝕜] Z, ∀ u : M, Th u = T u) ∧
    (M ≠ ⊥ → ∀ S : N →L[𝕜] Z, ∃ Sh : Y →L[𝕜] Z, ∀ v : N, Sh v = S v) := by sorry

end BilinearMapExtension.Complemented
