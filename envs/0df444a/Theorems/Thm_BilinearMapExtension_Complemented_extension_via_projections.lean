-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_extension_via_projections
-- name    : BilinearMapExtension.Complemented.extension_via_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:49.628176+00:00
-- url     : https://prove2.me/theorems/8ef39f0f-33b3-48e2-812a-a4d57971ce9c
-- title:
--   §5, proof of Theorem 5.2, p. 6 — φ̂(x, y) = φ̃(Ex, Py) extends φ, and ‖φ‖ ≤ ‖φ̂‖ ≤ ‖φ̃‖‖E‖‖P‖
-- statement:
--   Let $\mathcal M$ and $\mathcal N$ be linear manifolds of normed spaces $\mathcal X$ and $\mathcal Y$ over $\mathbb F\in\{\mathbb R,\mathbb C\}$ and let $\mathcal Z$ be a normed space. Let $E\in\mathcal B[\mathcal X,\mathcal X]$ and $P\in\mathcal B[\mathcal Y,\mathcal Y]$ be projections with $\mathcal R(E)=\mathcal M^-$ and $\mathcal R(P)=\mathcal N^-$. Let $\phi\in\boldsymbol b[\mathcal M\times\mathcal N,\mathcal Z]$ and let $\widetilde\phi\in\boldsymbol b[\mathcal M^-\times\mathcal N^-,\mathcal Z]$ extend $\phi$. Then the map
--   $$\widehat\phi(x,y) = \widetilde\phi(Ex, Py), \qquad (x,y)\in\mathcal X\times\mathcal Y,$$
--   belongs to $\boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z]$, extends $\phi$ ($\widehat\phi|_{\mathcal M\times\mathcal N}=\phi$), and
--   $$\|\phi\| \le \|\widehat\phi\| \le \|\widetilde\phi\|\,\|E\|\,\|P\|.$$
--
--   Together with the extension to the closures, this gives the sufficiency direction of Theorem 5.2(a) and, when $\|E\|=\|P\|=1$, the norm equality of Theorem 5.2(b).
--
--   **Formalization Note.** The conclusion asserts the existence of a bounded bilinear map given by the displayed formula, so the extension is the paper's one and the bound refers to it. The paper prints "$\mathcal R(E)=\mathcal M^-$ and $\mathcal R(E)=\mathcal N^-$" just above this step; the second is read as $\mathcal R(P)=\mathcal N^-$, which is what the construction uses. Completeness is not needed here because $\widetilde\phi$ is given.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 6, §5, proof of Theorem 5.2, (a2)⇒(a1) and (b)

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented

/-- §5, proof of Theorem 5.2, (a2)⇒(a1) and (b), p. 6: `φh(x, y) = φ̃(Ex, Py)` extends `φ` and
`‖φ‖ ≤ ‖φh‖ ≤ ‖φ̃‖‖E‖‖P‖`. -/
theorem extension_via_projections {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y)
    (E : X →L[𝕜] X) (P : Y →L[𝕜] Y)
    (hE : IsProjectionOnto E M.topologicalClosure) (hP : IsProjectionOnto P N.topologicalClosure)
    (φ : M →L[𝕜] N →L[𝕜] Z)
    (φt : M.topologicalClosure →L[𝕜] N.topologicalClosure →L[𝕜] Z)
    (hφt : ∀ (u : M) (v : N), φt (Submodule.inclusion M.le_topologicalClosure u)
      (Submodule.inclusion N.le_topologicalClosure v) = φ u v) :
    ∃ φh : X →L[𝕜] Y →L[𝕜] Z,
      (∀ x y, φh x y = φt ⟨E x, hE.1 x⟩ ⟨P y, hP.1 y⟩) ∧ IsBilinExtension M N φ φh ∧
      ‖φ‖ ≤ ‖φh‖ ∧ ‖φh‖ ≤ ‖φt‖ * ‖E‖ * ‖P‖ := by sorry

end BilinearMapExtension.Complemented
