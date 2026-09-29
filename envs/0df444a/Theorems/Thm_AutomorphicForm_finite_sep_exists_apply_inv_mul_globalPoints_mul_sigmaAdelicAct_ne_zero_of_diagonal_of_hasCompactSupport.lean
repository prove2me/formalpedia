-- Prove2me | Theorems.Thm_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport
-- name    : AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f8b3c1d8-94de-5b7d-82a8-45978addc1fe
-- title:
--   Finiteness of hyperbolic σ-twisted classes meeting a compact support
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so the extension is cyclic with generator $\sigma$). Let $D$ be an idèle-theoretic Galois descent datum for $L/K$, that is, a monoid homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adèle ring $\mathbb{A}_L$ of $L$ (formed with respect to $\mathcal{O}_L$) which is continuous in each argument and which restricts on the image of $L$ to the given Galois action. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ have compact support, and let $\Delta \subseteq \mathrm{GL}_2(L)$ be a set of elements $t$ such that each $t \in \Delta$ is diagonal (its $(1,0)$ and $(0,1)$ entries vanish) with $N_{L/K}(t_{00}/t_{11}) \neq 1$, and such that for distinct $t, t' \in \Delta$ the sets $\{\delta \in \mathrm{GL}_2(L) : \exists g \in \mathrm{GL}_2(L),\ t^{-1} g^{-1} \delta\, \sigma(g) \in Z(\mathrm{GL}_2(L))\}$ attached to $t$ and to $t'$ are disjoint, where $\sigma$ acts entrywise. Then the set of those $t \in \Delta$ for which there exist $x \in \mathrm{GL}_2(\mathbb{A}_L)$ and $z \in \mathbb{A}_L^\times$ with $\varphi\bigl(x^{-1} \cdot t_{\mathbb{A}} \cdot \sigma_{\mathbb{A}}(z\,I \cdot x)\bigr) \neq 0$ is finite; here $t_{\mathbb{A}}$ is the image of $t$ under the entrywise map induced by $L \to \mathbb{A}_L$, $z\,I$ is the scalar matrix with entry $z$, and $\sigma_{\mathbb{A}}$ is the entrywise map induced by the automorphism $D.\mathrm{act}\,\sigma$ of $\mathbb{A}_L$.
--
--   This is the finiteness statement needed for the hyperbolic contribution in the comparison of twisted orbital integrals for a cyclic extension $L/K$: only finitely many regular diagonal $\sigma$-twisted classes, taken up to central adèlic multiples, can meet the support of a compactly supported test function. It is used in the evaluation of the hyperbolic-cell integrals of a factorizable test function as a sum of orbital and weighted orbital terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_sigmaAdelicAct_ne_zero_of_diagonal_of_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    {t ∈ Δ | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite := by sorry
