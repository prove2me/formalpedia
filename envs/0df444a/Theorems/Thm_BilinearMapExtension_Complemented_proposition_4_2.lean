-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_proposition_4_2
-- name    : BilinearMapExtension.Complemented.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:49.546969+00:00
-- url     : https://prove2.me/theorems/9eab6cb1-a131-4796-9be2-f739028978bc
-- title:
--   Proposition 4.2, p. 3 — b[X×Y, Z] ≅ B[X, B[Y, Z]] isometrically, via φ ↦ (x ↦ φ(x, ·))
-- statement:
--   Let $\mathcal X, \mathcal Y, \mathcal Z$ be normed spaces over $\mathbb F \in \{\mathbb R,\mathbb C\}$. A bilinear map $\phi : \mathcal X\times\mathcal Y\to\mathcal Z$ is bounded if
--   $$\|\phi\| = \sup_{0\ne x\in\mathcal X,\ 0\ne y\in\mathcal Y} \frac{\|\phi(x,y)\|}{\|x\|\,\|y\|} < \infty,$$
--   and $\boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z]$ is the normed space of bounded bilinear maps with this norm. The proposition asserts that the natural map sending $\phi$ to $T$ with $T(x) = \phi(x,\cdot)$ is an isometric isomorphism
--   $$\boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z] \cong \mathcal B[\mathcal X,\mathcal B[\mathcal Y,\mathcal Z]].$$
--   Concretely:
--
--   1. every bilinear map $\phi$ with $\|\phi(x,y)\| \le C\|x\|\|y\|$ for some constant $C$ is represented by exactly one $T \in \mathcal B[\mathcal X,\mathcal B[\mathcal Y,\mathcal Z]]$, namely $T(x)(y) = \phi(x,y)$;
--   2. for every $T \in \mathcal B[\mathcal X,\mathcal B[\mathcal Y,\mathcal Z]]$ the operator norm of $T$ equals the bilinear norm above of $(x,y)\mapsto T(x)(y)$.
--
--   The paper uses this identification twice in the proof of Theorem 5.2 (with $\mathcal M\times\mathcal N$ and with $\mathcal M^-\times\mathcal N^-$ in place of $\mathcal X\times\mathcal Y$).
--
--   **Formalization Note.** This item is what licenses encoding every bounded bilinear map of the mission as a curried continuous linear map `X →L[𝕜] Y →L[𝕜] Z` with Mathlib's operator norm. In the supremum, Lean takes it over all $x, y$, with $a/0 = 0$; the terms with $x = 0$ or $y = 0$ are $0$ and, all terms being nonnegative, do not change the supremum, which is finite (bounded by $\|T\|$). The constant $C$ in (1) is any real number.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 3, Proposition 4.2 (norm of a bilinear map: §2, p. 2)

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

namespace BilinearMapExtension.Complemented

/-- Proposition 4.2, p. 3: `b[X×Y, Z] ≅ B[X, B[Y, Z]]` isometrically, via the natural map
`φ ↦ (x ↦ φ(x, ·))`. -/
theorem proposition_4_2 {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    (∀ f : X →ₗ[𝕜] Y →ₗ[𝕜] Z, (∃ C : ℝ, ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) →
      ∃! T : X →L[𝕜] Y →L[𝕜] Z, ∀ x y, T x y = f x y) ∧
    (∀ T : X →L[𝕜] Y →L[𝕜] Z, ‖T‖ = ⨆ (x : X) (y : Y), ‖T x y‖ / (‖x‖ * ‖y‖)) := by sorry

end BilinearMapExtension.Complemented
