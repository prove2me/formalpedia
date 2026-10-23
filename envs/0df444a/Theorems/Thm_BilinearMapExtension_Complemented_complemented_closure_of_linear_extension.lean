-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_complemented_closure_of_linear_extension
-- name    : BilinearMapExtension.Complemented.complemented_closure_of_linear_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:53.206992+00:00
-- url     : https://prove2.me/theorems/b95fff8f-c959-43a7-aa3a-6bab7d6436be
-- title:
--   §5, proof of Theorem 5.2, p. 5 (citing Megginson Thm 3.2.17) — if every nonzero T ∈ B[M, Z] extends to X for every Banach Z, then M⁻ is complemented
-- statement:
--   Let $\mathcal M$ be a linear manifold of a Banach space $\mathcal X$ over $\mathbb F\in\{\mathbb R,\mathbb C\}$. Suppose that for every Banach space $\mathcal Z$ and every nonzero $T\in\mathcal B[\mathcal M,\mathcal Z]$ there is $\widehat T\in\mathcal B[\mathcal X,\mathcal Z]$ with $\widehat T|_{\mathcal M} = T$. Then the closure $\mathcal M^-$ is a complemented subspace of $\mathcal X$:
--   $$\bigl(\forall \mathcal Z \text{ Banach},\ \forall T\in\mathcal B[\mathcal M,\mathcal Z]\setminus\{0\}\ \exists\widehat T\in\mathcal B[\mathcal X,\mathcal Z]:\ \widehat T|_{\mathcal M}=T\bigr)\ \Longrightarrow\ \mathcal M^- \text{ is complemented.}$$
--
--   The paper uses this classical fact (cited from Megginson, *An Introduction to Banach Space Theory*, Theorem 3.2.17) to finish the necessity direction of Theorem 5.2(a).
--
--   **Formalization Note.** The target spaces $\mathcal Z$ range over Banach spaces in the same universe as $\mathcal X$ (the natural choice $\mathcal Z = \mathcal M^-$ is a subtype of $\mathcal X$). The restriction to nonzero $T$ is kept as printed; it is the weaker hypothesis. When $\mathcal M = \{0\}$ the hypothesis is vacuous and the conclusion ($\{0\}$ is complemented by $\mathcal X$) holds.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 5, §5, proof of Theorem 5.2, (a1)⇒(a2), citing [17, Theorem 3.2.17]

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

universe u

namespace BilinearMapExtension.Complemented

/-- §5, proof of Theorem 5.2, (a1)⇒(a2), p. 5 (citing Megginson, Theorem 3.2.17). -/
theorem complemented_closure_of_linear_extension {𝕜 : Type*} [RCLike 𝕜] {X : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] (M : Submodule 𝕜 X)
    (h : ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
      (T : M →L[𝕜] Z), T ≠ 0 → ∃ Th : X →L[𝕜] Z, ∀ u : M, Th u = T u) :
    IsComplementedSubspace M.topologicalClosure := by sorry

end BilinearMapExtension.Complemented
