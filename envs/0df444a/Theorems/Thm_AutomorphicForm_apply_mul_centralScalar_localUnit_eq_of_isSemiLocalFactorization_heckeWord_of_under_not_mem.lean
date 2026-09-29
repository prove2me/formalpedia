-- Prove2me | Theorems.Thm_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
-- name    : AutomorphicForm.apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d675a8e8-af36-5f40-b218-ac2981afcbc4
-- title:
--   Central local-unit invariance of a semi-locally factorised test function
-- statement:
--   Let $L/K$ be a finite extension of number fields, let $S_K$ and $T$ be finite sets of finite places of $K$, and for each finite place $v$ of $K$ let $w_v =$ `ws v` be a place of $L$ above $v$ (an element of $v$`.Extension (𝓞 L)`, i.e. a finite place of $L$ whose contraction to $𝓞 K$ is $v$). Let $\varpi_v$ be an element of the valuation ring of $L_{w_v}$, nonzero in $L_{w_v}$ for $v \in T$, let $n_v$ be natural numbers and $r_v : \mathrm{Fin}(n_v) \to \mathrm{GL}_2(L_{w_v})$ a family which, for $v \in T$, is a Hecke coset system for the subgroup $\mathrm{GL}_2(\mathcal O_{w_v})$ (the image of `integralSubgroup`) and the element $\mathrm{diag}(\varpi_v,1)$: each $r_v(i)$ lies in the double coset, every element of the double coset shares a left coset with some $r_v(i)$, and $i \mapsto r_v(i)\,\mathrm{GL}_2(\mathcal O_{w_v})$ is injective. Let $z_v \in \mathrm{GL}_2(L_{w_v})$ be, for $v \in T$, the scalar matrix $\varpi_v \cdot 1$, and let $k_v, j_v$ be natural numbers. Let $\varphi_L$ on $\mathrm{GL}_2(\mathbb A_L)$, $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$, and $\varphi_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$ be complex-valued, and assume `IsSemiLocalFactorization` holds for $K, L$, the set $S_K \cup T$, $\varphi_L$, $\varphi_a$, $\varphi_f$ and the family of semi-local factors which at $v \in T$ is the Hecke word
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf 1_{\,\text{semi-local integral set at } v}\Big(\big(\text{semi-local component at } v \text{ of } \textstyle\prod_m r_v(\iota(m)) \cdot z_v^{\,j_v},\ \text{embedded at } w_v\big)^{-1} x\Big)$$
--   and at $v \notin T$ is $\varphi_v$; thus $\varphi_a$ is an archimedean test factor, $\varphi_f$ a finite test factor, each factor at a place of $S_K \cup T$ a semi-local test function, $\varphi_f(h)$ equals the product of the factors on the semi-local components of $h$ when all components outside $S_K \cup T$ are integral and vanishes when some such component is not, and $\varphi_L(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$. Then for every finite place $w$ of $L$ whose contraction to $𝓞 K$ is not in $S_K$, every unit $s$ of $L_w$ with valuation $1$, and every $g \in \mathrm{GL}_2(\mathbb A_L)$, one has $\varphi_L\big(g \cdot \mathrm{diag}(\tilde s, \tilde s)\big) = \varphi_L(g)$, where $\tilde s$ is the idele which is $s$ at $w$ and $1$ at all other places, finite and infinite.
--
--   This is the right-invariance of a semi-locally factorised Hecke-word test function on $\mathrm{GL}_2(\mathbb A_L)$ under translation by a central idele supported at a single finite place where it is a unit; the factor at a place of $T$ is the characteristic function of a translated integral set, which is stable under such translation, so no condition at $T$ is needed. It is used as an input to the winding computation in [`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K)))
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
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
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φL : AdelicGL2 (𝓞 L) L → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hSLF : AutomorphicForm.IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (ns v),
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
        else φS v))
    (w : HeightOneSpectrum (𝓞 L)) (hw : HeightOneSpectrum.under (𝓞 K) w ∉ SK)
    (s : (w.adicCompletion L)ˣ) (hs : Valued.v (s : w.adicCompletion L) = 1)
    (g : AdelicGL2 (𝓞 L) L) :
    φL (g * AutomorphicForm.centralScalar (𝓞 L) L
      (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w s))) = φL g := by sorry
