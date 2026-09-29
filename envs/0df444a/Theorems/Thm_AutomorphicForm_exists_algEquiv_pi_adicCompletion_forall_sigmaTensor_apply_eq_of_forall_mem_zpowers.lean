-- Prove2me | Theorems.Thm_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
-- name    : AutomorphicForm.exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/871a83e8-0acf-5967-8750-19e2131fff31
-- title:
--   Twisted-shift decomposition of L⊗_K Kᵥ for cyclic L/K
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a Galois extension, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in `Subgroup.zpowers σ` (so the Galois group is cyclic with generator $\sigma$), let $v$ be a height-one prime of $\mathcal{O}_K$ and let $w$ be an extension of $v$ to $\mathcal{O}_L$, that is, a height-one prime of $\mathcal{O}_L$ lying under $v$ over $\mathcal{O}_K$. The assertion is that there exist a natural number $m$, an automorphism $\theta$ of $L_w :=$ `w.1.adicCompletion L` as an algebra over $K_v :=$ `v.adicCompletion K`, and an isomorphism $\Psi$ of $K_v$-algebras from $L \otimes_K K_v$ (with $K_v$ acting through the right factor) onto $\mathrm{Fin}(m+1) \to L_w$, such that: (i) $\Psi$ conjugates the ring endomorphism `sigmaTensor`, namely $\sigma \otimes \mathrm{id}_{K_v}$, into the shift twisted by $\theta$: for every $z$ and every $k : \mathrm{Fin}\,m$ one has $\Psi(\sigma\otimes 1)(z)$ at $k$ (via `Fin.castSucc`) equal to $\Psi(z)$ at $k+1$ (via `Fin.succ`), and $\Psi(\sigma\otimes 1)(z)$ at the last index equals $\theta(\Psi(z)_0)$; (ii) $z$ lies in `semiLocalIntegers`, the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v$ in $L\otimes_K K_v$ under `tensorAdicCompletionIntegersTo`, if and only if every coordinate $\Psi(z)_j$ lies in `w.1.adicCompletionIntegers L`; (iii) for $x \in L$ and each index $j$, $\Psi(x \otimes 1)_j$ is the image of $\sigma^j x$ under $L \to L_w$; (iv) the order of $\theta$ equals $[L_w:K_v]$; (v) $\theta y = y$ exactly for $y$ in the image of $K_v \to L_w$; (vi) $\theta$ preserves the valuation, $\mathrm{v}(\theta y) = \mathrm{v}(y)$; (vii) $(m+1)\,[L_w:K_v] = [L:K]$; and (viii) the number of extensions of $v$ to $\mathcal{O}_L$ is $m+1$.
--
--   This is the semi-local decomposition of $L \otimes_K K_v$ for a cyclic extension of number fields, in the explicit coordinate-wise form in which the generator of the Galois group becomes a cyclic shift of the $m+1$ factors twisted by a generator $\theta$ of $\mathrm{Gal}(L_w/K_v)$, together with the matching statements for the semi-local integers, the embeddings of $L$, the valuation and the degree and place counts. It is used in the estimate for twisted orbital integrals of the indicator function of the semi-local integral set in the unramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    ∃ (m : ℕ) (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (Ψ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L)),
      (∀ z : L ⊗[K] v.adicCompletion K,
        (∀ k : Fin m, Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc = Ψ z k.succ) ∧
          Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) = θ (Ψ z 0)) ∧
      (∀ z : L ⊗[K] v.adicCompletion K,
        z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Ψ z j ∈ w.1.adicCompletionIntegers L) ∧
      (∀ (x : L) (j : Fin (m + 1)),
        Ψ (x ⊗ₜ[K] (1 : v.adicCompletion K)) j = algebraMap L (w.1.adicCompletion L) ((σ ^ (j : ℕ)) x)) ∧
      orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ∧
      (∀ y : w.1.adicCompletion L,
        θ y = y ↔ y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      (∀ y : w.1.adicCompletion L, Valued.v (θ y) = Valued.v y) ∧
      (m + 1) * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Nat.card (v.Extension (𝓞 L)) = m + 1 := by sorry
