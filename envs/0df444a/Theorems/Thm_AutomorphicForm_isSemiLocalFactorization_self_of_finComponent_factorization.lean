-- Prove2me | Theorems.Thm_AutomorphicForm_isSemiLocalFactorization_self_of_finComponent_factorization
-- name    : AutomorphicForm.isSemiLocalFactorization_self_of_finComponent_factorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/d3a12678-3f0f-5a71-ad32-deb80fc50034
-- title:
--   Semi-local factorisation over K/K of Hecke-word test functions
-- statement:
--   Let $K$ be a number field, and let $S,T$ be finite sets of finite places of $K$. Given a function $f_a$ on $\mathrm{GL}_2$ of the infinite adele ring, a family $f_{S,v}$ of functions on $\mathrm{GL}_2(K_v)$, lengths $n_v\in\mathbb N$, elements $r_{v,0},\dots,r_{v,n_v-1}$ and $z_v$ of $\mathrm{GL}_2(K_v)$, exponents $e_0(v),e_1(v)\in\mathbb N$ for $v\in T$, and functions $\varphi$ on $\mathrm{GL}_2$ of the adele ring and $f_f$ on $\mathrm{GL}_2$ of the finite adele ring, assume: $f_a$ has compact support and is given by a smooth function of its matrix entries read in the mixed space; each $f_{S,v}$ with $v\in S$ is locally constant with compact support; $f_f$ is locally constant with compact support; whenever every component of $h$ at $v\notin S\cup T$ lies in the integral-units set of $\mathcal O_v$, $f_f(h)=\prod_{v\in S\cup T}$ of the local factor at the $v$-component, this factor being, for $v\in T$, $x\mapsto\sum_{\iota:\mathrm{Fin}(e_0(v))\to\mathrm{Fin}(n_v)}\mathbf 1_{\mathrm{GL}_2(\mathcal O_v)}\bigl((\prod_m r_{v,\iota(m)}\cdot z_v^{e_1(v)})^{-1}x\bigr)$ and, for $v\in S\setminus T$, $f_{S,v}$; $f_f(h)=0$ as soon as some $v\notin S\cup T$ has non-integral component; and $\varphi(g)=f_a(g_\infty)f_f(g_{\mathrm{fin}})$. The conclusion is `IsSemiLocalFactorization K K (S ∪ T) φ fa ff` for the semi-local factors on $\mathrm{GL}_2(K\otimes_K K_v)$ defined by the same word indicator, written with the semi-local integral-units set and the semi-local component of the local embedding of the word (exponents $e_0(v),e_1(v)$ for $v\in T$, and $0$ otherwise), for $v\in T$, and by $f_{S,v}$ transported along evaluation of the base-change isomorphism $K\otimes_K K_v\cong\prod_{w\mid v}K_w$ at the tautological extension of $v$, for $v\notin T$; that is, $f_a$ and $f_f$ are test factors, each semi-local factor is locally constant with compact support, $f_f$ is the product of the semi-local factors at the semi-local components on the points integral outside $S\cup T$, vanishes elsewhere, and $\varphi$ splits as $f_a\cdot f_f$.
--
--   This is the degeneration of the semi-local factorisation vocabulary to the trivial extension $K/K$: a purely local factorisable test function, with Hecke-word indicators at the places of $T$, is repackaged as a semi-local factorisation over $K\otimes_K K_v$ at $S\cup T$. It feeds the orbital-integral and trace-comparison statements that are phrased in semi-local terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isSemiLocalFactorization_self_of_finComponent_factorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isSemiLocalFactorization_self_of_finComponent_factorization
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) (v.adicCompletion K))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (e₀ e₁ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T → ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfa : IsArchTestFactor K fa) (hfS : ∀ v ∈ S, IsLocalTestFn K v (fS v)) (hff : IsFinTestFactor K ff)
    (hprod : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ S ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
        ff h = ∏ v ∈ S ∪ T,
          (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin (e₀ v hv) → Fin (ns v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rs v (ι m)).prod * zs v ^ (e₁ v hv))⁻¹ * x)
            else fS v) (AdelicLevel.finComponent (𝓞 K) K v h))
    (hvan : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ S ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0)
    (hφ : ∀ g, φ g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)) :
    IsSemiLocalFactorization K K (S ∪ T) φ fa ff
      (fun v => if v ∈ T then fun x : GL (Fin 2) (K ⊗[K] v.adicCompletion K) =>
          ∑ ι : Fin (if hv : v ∈ T then e₀ v hv else 0) → Fin (ns v),
            (semiLocalIntegralSet K K v).indicator (fun _ => (1 : ℂ))
              ((semiLocalComponent K K v (AdelicDock.localEmbed (𝓞 K) K v
                ((List.ofFn fun m => rs v (ι m)).prod * zs v ^ (if hv : v ∈ T then e₁ v hv else 0))))⁻¹ * x)
        else fun x : GL (Fin 2) (K ⊗[K] v.adicCompletion K) =>
          fS v (Matrix.GeneralLinearGroup.map
              ((Pi.evalRingHom (fun w : v.Extension (𝓞 K) => w.1.adicCompletion K) (⟨v, HeightOneSpectrum.ext (Ideal.comap_id v.asIdeal)⟩ : v.Extension (𝓞 K))).comp
                (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K K (𝓞 K) v).toRingEquiv.toRingHom) x)) := by sorry
