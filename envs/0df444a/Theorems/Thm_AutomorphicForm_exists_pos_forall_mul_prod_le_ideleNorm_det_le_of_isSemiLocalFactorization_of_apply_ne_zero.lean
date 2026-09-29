-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
-- name    : AutomorphicForm.exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/387767d4-1e4c-5e5c-821e-a3c74cdec6f0
-- title:
--   Idèle norm of det g on the support of Hecke words
-- statement:
--   Let $K\subseteq L$ be number fields, let $S$ and $T$ be finite sets of height-one primes of $\mathcal O_K$, let $\varphi_a$ be a function on $\mathrm{GL}_2$ of the infinite adele ring of $L$, and for each height-one prime $v$ of $\mathcal O_K$ let $\varphi_{S,v}$ be a function on $\mathrm{GL}_2(L\otimes_K K_v)$. Suppose given, for each $v$, an extension $w_v$ of $v$ to $\mathcal O_L$ (a height-one prime of $\mathcal O_L$ lying under $v$), an element $\varpi_v$ of the valuation ring of $L_{w_v}$, a natural number $n_v$, elements $r_{v,0},\dots,r_{v,n_v-1}$ of $\mathrm{GL}_2(L_{w_v})$ and an element $z_v\in\mathrm{GL}_2(L_{w_v})$, such that for $v\in T$: $\varpi_v$ is irreducible with nonzero image in $L_{w_v}$; the family $(r_{v,i})_i$ is a Hecke coset system for the subgroup $U_v=\mathrm{im}\bigl(\mathrm{GL}_2(\mathcal O_{w_v})\to\mathrm{GL}_2(L_{w_v})\bigr)$ and the element $\mathrm{diag}(\varpi_v,1)$, i.e. each $r_{v,i}$ lies in the double coset $U_v\,\mathrm{diag}(\varpi_v,1)\,U_v$, every element of that double coset lies in some $r_{v,i}U_v$, and $i\mapsto r_{v,i}U_v$ is injective; and the matrix of $z_v$ equals $\varpi_v\cdot 1$. Then there are reals $m,M$ with $0<m$ such that for all profiles $(k_v)_v,(j_v)_v$ of natural numbers and all $\varphi$ on $\mathrm{GL}_2(\mathbb A_L)$, $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ the following holds. Assume [`AutomorphicForm.IsSemiLocalFactorization`](def/AutomorphicForm_TwistedOrbital.html#L452) for $K,L$, the set $S\cup T$, $\varphi$, $\varphi_a$, $\varphi_f$ and the local data which at $v\in T$ is the Hecke word $$x\mapsto\sum_{\iota:\{0,\dots,k_v-1\}\to\{0,\dots,n_v-1\}}\mathbf 1_{\Sigma_v}\Bigl(\bigl(\text{semi-local component at }v\text{ of }\iota\text{-word}\bigr)^{-1}x\Bigr),$$ where the $\iota$-word is the image under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) at $w_v$ of $r_{v,\iota(0)}\cdots r_{v,\iota(k_v-1)}z_v^{\,j_v}$ and $\Sigma_v$ is the set of elements of $\mathrm{GL}_2(L\otimes_K K_v)$ whose matrix and inverse matrix have entries in the image of $\mathcal O_L\otimes\mathcal O_v$, and which at $v\notin T$ is $\varphi_{S,v}$; that is, $\varphi_a$ is a compactly supported smooth function of the archimedean matrix entries, $\varphi_f$ is locally constant with compact support, the data at each $v\in S\cup T$ is a semi-local test function, $\varphi_f(h)$ equals the product over $v\in S\cup T$ of the local data evaluated at the semi-local components of $h$ whenever all components of $h$ outside $S\cup T$ are integral, $\varphi_f(h)=0$ as soon as some component outside $S\cup T$ is not integral, and $\varphi(g)=\varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$. Then for every $g\in\mathrm{GL}_2(\mathbb A_L)$ with $\varphi(g)\neq 0$, writing $P=\prod_{v\in T}N(w_v)^{-(k_v+2j_v)}$ with $N(w_v)$ the absolute norm of the ideal $w_v$, one has $mP\le \|\det g\|_{\mathbb A_L}\le MP$, the idèle norm being the value of the distributive Haar character of the adele ring of $L$ at $\det g$.
--
--   This is the support-and-determinant computation underlying bounds for orbital integrals of Hecke words: the constants $m$ and $M$ depend only on the fixed archimedean and non-$T$ data, while the dependence on the profile $(k_v,j_v)$ is exactly the factor $\prod_{v\in T}N(w_v)^{-(k_v+2j_v)}$ coming from the determinants of the double-coset representatives and of the central elements $z_v$. It is used by [`AutomorphicForm.exists_forall_norm_apply_le_mul_prod_of_isSemiLocalFactorization_of_apply_ne_zero`](thm.html#AutomorphicForm.exists_forall_norm_apply_le_mul_prod_of_isSemiLocalFactorization_of_apply_ne_zero), and its proof rests on the expression of the idèle norm as a product of local absolute values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hϖs : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T,
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) :
    ∃ m M : ℝ, 0 < m ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        AutomorphicForm.IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        ∀ g : GL (Fin 2) (AdeleRing (𝓞 L) L), φ g ≠ 0 →
          m * ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) ≤
              NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∧
            NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤
              M * ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) := by sorry
