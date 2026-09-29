-- Prove2me | Theorems.Thm_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd
-- name    : CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/ba971d58-dc97-55ae-a8d4-f922ce0f905d
-- title:
--   Congruence characters of Γ₀(N) are Eisenstein at good ℓ
-- statement:
--   Fix a natural number $N$ and an additive abelian group $A$, and let $\varphi$ be an element of [`CohCarrier.H1 N ⊤ A`](def/CohCarrier_Level.html#L162), that is, an additive homomorphism from `Additive ↥(CohCarrier.GammaH N ⊤)` to $A$; here `GammaH N ⊤` is the subgroup of $\mathrm{SL}_2(\mathbb Z)$ obtained by taking the preimage of the full subgroup of $(\mathbb Z/N)^\times$ under the character `gamma0Units N` on $\Gamma_0(N)$ and pushing it forward along the inclusion of $\Gamma_0(N)$, so that $\varphi$ is just a homomorphism from $\Gamma_0(N)$ to $A$. Let $M$ be a natural number with $0 < M$, and assume that $\varphi$ vanishes on every $\gamma \in$ `GammaH N ⊤` whose underlying matrix in $\mathrm{SL}_2(\mathbb Z)$ lies in the principal congruence subgroup $\Gamma(M)$ (`CongruenceSubgroup.Gamma M`). Let $\ell$ be a nonzero natural number which is prime and divides neither $N$ nor $M$. Then $\varphi$ is fixed up to the factor $\ell + 1$ by the operator [`CohCarrier.heckeT N ⊤ ℓ A`](def/CohCarrier_Level.html#L250), namely the transfer to `GammaH N ⊤` of the precomposition of $\varphi$ with the homomorphism [`CohCarrier.conjL N ⊤ ℓ`](def/CohCarrier_Level.html#L228) from `GammaHUpper N ⊤ ℓ` to `GammaH N ⊤` induced by the matrix conjugation `conjUpperMat ℓ`: one has `heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ`, with no hypothesis on the torsion of $A$.
--
--   This is the case of a prime away from the congruence level of the assertion that congruence characters of $\Gamma_0(N)$ — homomorphisms to $A$ trivial on $\Gamma_0(N) \cap \Gamma(M)$ — are Eisenstein, the Hecke operator $T_\ell$ acting on them by the scalar $\ell+1$. It is used by [`CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero`](thm.html#CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero), which removes the coprimality restriction on $\ell$, in the cohomological treatment of Ihara's lemma with arbitrary coefficients; the proof invokes the surjectivity of reduction $\mathrm{SL}_2(\mathbb Z) \to \mathrm{SL}_2(\mathbb Z/N)$, the computation `index_GammaHUpper_of_prime` of the index $\ell+1$, and the identity `coresAdd_comp_subtype` expressing the transfer of a restricted character as multiplication by the index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero_of_not_dvd
    (N : ℕ) (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (M : ℕ) (hM : 0 < M) (hφ : ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M → φ (Additive.ofMul γ) = 0)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓM : ¬ ℓ ∣ M) :
    CohCarrier.heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ := by sorry
