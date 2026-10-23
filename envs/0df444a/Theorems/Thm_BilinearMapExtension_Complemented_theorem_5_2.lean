-- Prove2me | Theorems.Thm_BilinearMapExtension_Complemented_theorem_5_2
-- name    : BilinearMapExtension.Complemented.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:52.38+00:00
-- url     : https://prove2.me/theorems/1c57ae1d-4b4f-42f1-937a-49e16a8e8e94
-- title:
--   Theorem 5.2, p. 5 — bounded bilinear maps on M×N extend to X×Y for every Banach Z iff M⁻ and N⁻ are complemented; norm-one projections preserve the norm
-- statement:
--   Let $\mathcal M$ and $\mathcal N$ be linear manifolds (not necessarily closed) of Banach spaces $\mathcal X$ and $\mathcal Y$ over $\mathbb F\in\{\mathbb R,\mathbb C\}$, with closures $\mathcal M^-$ and $\mathcal N^-$.
--
--   **(a)** Assume $\mathcal M\ne\{0\}$ and $\mathcal N\ne\{0\}$. Every bounded bilinear map $\phi:\mathcal M\times\mathcal N\to\mathcal Z$ into an arbitrary Banach space $\mathcal Z$ has a bounded bilinear extension $\widehat\phi:\mathcal X\times\mathcal Y\to\mathcal Z$ if and only if $\mathcal M^-$ and $\mathcal N^-$ are complemented subspaces of $\mathcal X$ and $\mathcal Y$:
--   $$\Bigl(\forall\,\mathcal Z\text{ Banach},\ \forall\,\phi\in\boldsymbol b[\mathcal M\times\mathcal N,\mathcal Z]\ \ \exists\,\widehat\phi\in\boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z]:\ \widehat\phi|_{\mathcal M\times\mathcal N}=\phi\Bigr)\iff \mathcal M^-,\ \mathcal N^- \text{ complemented}.$$
--
--   **(b)** If $\mathcal M^-=\mathcal R(E)$ and $\mathcal N^-=\mathcal R(P)$ for projections $E\in\mathcal B[\mathcal X,\mathcal X]$ and $P\in\mathcal B[\mathcal Y,\mathcal Y]$ with $\|E\|=\|P\|=1$, then for every Banach space $\mathcal Z$ every $\phi\in\boldsymbol b[\mathcal M\times\mathcal N,\mathcal Z]$ has a bounded bilinear extension $\widehat\phi$ to $\mathcal X\times\mathcal Y$ with
--   $$\|\widehat\phi\| = \|\phi\|.$$
--
--   The theorem is a Hahn–Banach type result for vector-valued bilinear maps: unlike linear functionals, bilinear maps do not extend in general, and the obstruction is exactly the failure of complementation of the closures.
--
--   **Formalization Note.** The assumption $\mathcal M,\mathcal N\ne\{0\}$ in (a) is taken from the first line of the paper's proof; without it the forward implication fails (if $\mathcal N=\{0\}$ every $\phi$ is $0$ and extends, while $\mathcal M^-$ need not be complemented, e.g. $c_0\subseteq\ell^\infty$). Part (b) does not need it. The Banach targets $\mathcal Z$ range over types in the universe of $\mathcal X$ and $\mathcal Y$ (the forward direction uses $\mathcal Z = \mathcal M^-$). In (b) the conclusion is the existence of an extension of equal norm: extensions are not unique and need not all have norm $\|\phi\|$. Projections are bounded operators mapping onto the closure and fixing it pointwise; complementation demands a *closed* complement. Bilinear maps are curried continuous linear maps with the operator norm (Proposition 4.2).
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, p. 5, Theorem 5.2 (nonzero M, N: first line of its proof, p. 5)

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

universe u

namespace BilinearMapExtension.Complemented

/-- Theorem 5.2, p. 5. -/
theorem theorem_5_2 {𝕜 : Type*} [RCLike 𝕜] {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y) :
    -- (a), for nonzero  and  (the opening line of the proof)
    (M ≠ ⊥ → N ≠ ⊥ →
      ((∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
          (φ : M →L[𝕜] N →L[𝕜] Z), ∃ φh : X →L[𝕜] Y →L[𝕜] Z, IsBilinExtension M N φ φh) ↔
        (IsComplementedSubspace M.topologicalClosure ∧
          IsComplementedSubspace N.topologicalClosure))) ∧
    -- (b)
    (∀ (E : X →L[𝕜] X) (P : Y →L[𝕜] Y),
      IsProjectionOnto E M.topologicalClosure → IsProjectionOnto P N.topologicalClosure →
      ‖E‖ = 1 → ‖P‖ = 1 →
      ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
        (φ : M →L[𝕜] N →L[𝕜] Z),
        ∃ φh : X →L[𝕜] Y →L[𝕜] Z, IsBilinExtension M N φ φh ∧ ‖φh‖ = ‖φ‖) := by sorry

end BilinearMapExtension.Complemented
