-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
-- name    : AutomorphicForm.exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/7dcdfe54-3988-5bc9-be0f-a5e7c559c96d
-- title:
--   Uniform bound on elliptic–central twisted kernel terms off the identity family
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be an automorphism in $\mathrm{Gal}(L/K)$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so the Galois group is cyclic with generator $\sigma$). Let $D$ be an idelic Galois descent datum for $L/K$, that is, a monoid homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$ which acts on principal adeles through the Galois action on $L$ and is continuous for each group element; write $\sigma_{\mathbb{A}}$ for the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}\,\sigma$ entrywise. Let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ have compact support. Then there is a natural number $N$ such that for every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ and every idele $z \in \mathbb{A}_L^{\times}$ the set of $\delta \in \mathrm{GL}_2(L)$ satisfying the following three conditions has at most $N$ elements (its `encard` is $\le N$): first, there exists $\gamma \in \mathrm{GL}_2(K)$ whose matrix either has characteristic polynomial with no root in $K$ (the elliptic cell) or is a scalar multiple of the identity (the central cell), such that the norm class of the $\sigma$-twisted conjugacy class of $\delta$ — the image under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) of the class of $\delta$ modulo the relation $\delta' = h^{-1}\,\delta\,\sigma(h)$, namely the $\mathrm{GL}_2(K)$-conjugacy class of the chosen norm representative `normRep hgen δ` — equals the conjugacy class of $\gamma$; second, $\delta$ is not of the form $u \cdot h^{-1}\,\sigma(h)$ with $u \in L^{\times}$ acting as a scalar matrix and $h \in \mathrm{GL}_2(L)$; and third, $\varphi\bigl(x^{-1}\,\iota(\delta)\,\sigma_{\mathbb{A}}(\underline{z}\,x)\bigr) \neq 0$, where $\iota$ is the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$ and $\underline{z}$ is the central scalar matrix attached to $z$.
--
--   This is the twisted analogue of the support lemma for the elliptic part of the kernel on the geometric side of the trace formula: the set of contributing $\delta$ varies with $(x,z)$, but its cardinality is bounded uniformly. It is used in the proof of [`AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top`](thm.html#AutomorphicForm.lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top), the finiteness of the integral of the elliptic-and-central-norm part of the $\sigma$-twisted kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ) :
    ∃ N : ℕ, ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      {δ : GL (Fin 2) L |
        (∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
            ConjClasses.mk γ) ∧
        (¬ ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
            (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) ∧
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.encard
        ≤ N := by sorry
