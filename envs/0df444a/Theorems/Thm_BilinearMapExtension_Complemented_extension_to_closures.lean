-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_extension_to_closures
-- name    : BilinearMapExtension.Complemented.extension_to_closures
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:56.659522+00:00
-- url     : https://prove2.me/theorems/c9bcdb4e-f993-4ad1-8bd3-335e6643c279
-- title:
--   §5, proof of Theorem 5.2, p. 6 — every φ ∈ b[M×N, Z], Z Banach, extends to φ̃ ∈ b[M⁻×N⁻, Z] with ‖φ̃‖ = ‖φ‖
-- statement:
--   Let $\mathcal M$ and $\mathcal N$ be linear manifolds of normed spaces $\mathcal X$ and $\mathcal Y$ over $\mathbb F\in\{\mathbb R,\mathbb C\}$, with closures $\mathcal M^-$ and $\mathcal N^-$, and let $\mathcal Z$ be a Banach space. Every bounded bilinear map $\phi\in\boldsymbol b[\mathcal M\times\mathcal N,\mathcal Z]$ has a bounded bilinear extension $\widetilde\phi\in\boldsymbol b[\mathcal M^-\times\mathcal N^-,\mathcal Z]$ of the same norm:
--   $$\widetilde\phi|_{\mathcal M\times\mathcal N} = \phi, \qquad \|\widetilde\phi\| = \|\phi\|.$$
--
--   This is the first half of the sufficiency direction of Theorem 5.2(a), and the source of the equality $\|\widehat\phi\| = \|\phi\|$ in Theorem 5.2(b).
--
--   **Formalization Note.** Bilinear maps on $\mathcal M^-\times\mathcal N^-$ are continuous linear maps `M.topologicalClosure →L[𝕜] N.topologicalClosure →L[𝕜] Z`; "$\widetilde\phi$ restricts to $\phi$" is stated through the inclusions $\mathcal M\hookrightarrow\mathcal M^-$, $\mathcal N\hookrightarrow\mathcal N^-$. The norms are Mathlib operator norms, equal to the paper's bilinear norms by Proposition 4.2. A printed slip in the paper's norm computation (the first supremum reads $\phi(\widetilde u,\widetilde v)$ for $\widetilde\phi(\widetilde u,\widetilde v)$) does not affect the statement.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 6, §5, proof of Theorem 5.2, (a2)⇒(a1) and (b)

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented

/-- §5, proof of Theorem 5.2, (a2)⇒(a1) and (b), p. 6: `φ` extends to `φ̃ ∈ b[M⁻×N⁻, Z]` with
`‖φ̃‖ = ‖φ‖`. -/
theorem extension_to_closures {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
    (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y) (φ : M →L[𝕜] N →L[𝕜] Z) :
    ∃ φt : M.topologicalClosure →L[𝕜] N.topologicalClosure →L[𝕜] Z,
      (∀ (u : M) (v : N), φt (Submodule.inclusion M.le_topologicalClosure u)
        (Submodule.inclusion N.le_topologicalClosure v) = φ u v) ∧ ‖φt‖ = ‖φ‖ := by sorry

end BilinearMapExtension.Complemented
