-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub_unram
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/09721095-5469-5a64-8f7f-01ec99fa1b37
-- title:
--   Asymptotic twisted spectral identity for GL₂, ramified places in S_L
-- statement:
--   Throughout, $L/K$ is a finite Galois extension of number fields, $\mathbf{A}_L$ denotes the adele ring of $L$, and $\Sigma_{\alpha,\beta}=\{g\in\mathrm{GL}_2(\mathbf{A}_L)\mid \mathtt{NumberField.TateGlobal.ideleNorm}\,L(\det g)\in[\alpha,\beta]\}$ is the determinant slab, the idele norm being the value of the distributive Haar character of $\mathbf{A}_L$ at the given idele.
--
--   **Carriers and measures.** Real numbers $\alpha<\beta$ with $\alpha>0$ (`hα`, `hαβ`) are fixed. A set $\Phi_L\subseteq\mathrm{GL}_2(\mathbf{A}_L)$ is given with $\Phi_L\subseteq\Sigma_{\alpha,\beta}$ (`hΦs`) which, by `hΦ`, is a fundamental domain for the range of `globalPoints`, i.e. for the image of $\mathrm{GL}_2(L)$ under the map induced by $L\to\mathbf{A}_L$, with respect to `adelicGLHaar` restricted to $\Sigma_{\alpha,\beta}$. On the idele group $\mathbf{A}_L^\times$, equipped with a Borel measurable structure, a Haar measure $\nu_{Z_L}$ is given together with a set $\Omega_L$ which by `hΩL` is a fundamental domain for the image of $L^\times$ in $\mathbf{A}_L^\times$ with respect to $\nu_{Z_L}$.
--
--   **Galois data.** $D$ is an element of [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28): a homomorphism $\tau\mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbf{A}_L$, compatible with $\tau$ on the image of $L$ and continuous for each $\tau$. An automorphism $\sigma\in\mathrm{Gal}(L/K)$ is given with `hgen`: every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, so the Galois group is cyclic with generator $\sigma$.
--
--   **Places, character, level, types.** $S_L$ is a finite set of finite places of $L$ subject to two conditions: `hSLram` requires that every $w$ for which the ramification index of $w.\mathrm{asIdeal}$ over the prime of $\mathcal{O}_K$ beneath it is different from $1$ lies in $S_L$ (so $S_L$ contains all places ramified in $L/K$), and `hSL` requires $S_L$ to be a union of fibres: places $w,w'$ of $L$ lying over the same place of $K$ belong to $S_L$ together or not at all. $\xi_L$ is a homomorphism from the top subgroup of $\mathbf{A}_L^\times$ to $\mathbb{C}^\times$, with `hξc` the continuity of $z\mapsto\xi_L(z)$ as a complex-valued function and `hξt` its triviality on the image of $L^\times$. $N$ is an ideal of $\mathcal{O}_L$ with `hN`: every finite place of $L$ whose prime divides $N$ lies in $S_L$. Further, `tysL` is an `ArchTypeFamily` for $L$ (a number $\mathrm{card}\,w$ of archimedean types at each infinite place $w$ together with the corresponding representations), $S$ is a finite set of finite places of $K$, $\varphi_a$ a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S$ assigns to each finite place $v$ of $K$ a function on $\mathrm{GL}_2(L\otimes_K K_v)$.
--
--   **Table set.** $X$ is a set of tables, i.e. of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$, and `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for $w\in S_L$ and such that for $w\notin S_L$, writing $\xi_w=\xi_L(\det(\mathtt{heckeGen}\,w))$: the second entry satisfies $(x_w)_2=\mathtt{HeckeEigensystem.cNorm}\,w\cdot\xi_w$ (the absolute norm of $w$ times $\xi_w$), the first satisfies $\lVert (x_w)_1\rVert\le(\mathrm{N}(w)+1)\sqrt{\lVert\xi_w\rVert}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\lVert (x_w)_2\rVert\bigr)\cdot (x_w)_1$.
--
--   **Siegel data.** Real numbers $c,u,d_1,d_2$ with $c>0$ (`hc`), a compact set $T_c\subseteq\mathrm{GL}_2(\mathbf{A}_L)$ and a second set $\Phi_0$ are given, subject to: `hΦ₀S`, that $\Phi_0$ is contained in the union over $y\in T_c$ of the right translates by $y$ of `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (the set of $g$ whose finite part is integral and which at every infinite place have local height at least $c$, window quantity at most $u^2$, and archimedean determinant norm in $[d_1,d_2]$); `hΦ₀s`, that $\Phi_0\subseteq\Sigma_{\alpha,\beta}$; and `hΦ₀`, that $\Phi_0$ is again a fundamental domain for the image of $\mathrm{GL}_2(L)$ with respect to `adelicGLHaar` restricted to $\Sigma_{\alpha,\beta}$.
--
--   **Conclusion.** There exist a sequence of tables $\mathrm{tabs}:\mathbb{N}\to(\text{finite places of }L\to\mathbb{C}\times\mathbb{C})$ with $\mathrm{tabs}\,n\in X$ for all $n$, and complex coefficients $\mathrm{cs}:\mathbb{N}\to\mathbb{C}$, such that the following three assertions hold.
--
--   (1) $\sum_n\lVert \mathrm{cs}\,n\rVert$ converges.
--
--   (2) For every $n$ with $\mathrm{cs}\,n\ne0$: first, $\mathrm{tabs}\,n$ is constant on fibres away from $S_L$, i.e. $\mathrm{tabs}\,n\,w=\mathrm{tabs}\,n\,w'$ whenever $w,w'\notin S_L$ lie over the same place of $K$; and second, there are an ideal $M\ne\bot$ of $\mathcal{O}_L$ and homomorphisms $\chi_1,\chi_2:\mathbf{A}_L^\times\to\mathbb{C}^\times$, each continuous as a complex-valued function and each trivial on the image of $L^\times$, such that for every $w\notin S_L$ the pair $\mathrm{tabs}\,n\,w$ equals the $w$-entries $(a_w,b_w)$ of [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), that is $a_w=\chi_1(\varpi_w)+\chi_2(\varpi_w)$ and $b_w=\chi_1(\varpi_w)\chi_2(\varpi_w)$ with $\varpi_w$ the uniformiser idele at $w$; thus the atoms are Eisenstein tables of level $M$.
--
--   (3) For every finite set $T$ of finite places of $K$ with $T$ disjoint from $S$, $\#T\ge2$, and such that no place of $L$ above a place of $T$ lies in $S_L$; for every choice of an extension $\mathrm{ws}\,v$ to $L$ of each place $v$ of $K$ and of a map $w'$ from places of $K$ to finite places of $L$ with $(w'v).\mathrm{asIdeal}=\sigma^{-1}\cdot(\mathrm{ws}\,v)_1.\mathrm{asIdeal}$ for $v\in T$; for every family $\varpi$ of elements of the valuation ring of $L$ at $(\mathrm{ws}\,v)_1$ which for $v\in T$ are irreducible and have nonzero image in the completion (`hϖs0`); for all $\mathrm{ns}$ and families $\mathrm{rTs}\,v:\mathrm{Fin}(\mathrm{ns}\,v)\to\mathrm{GL}_2$ of the completion at $(\mathrm{ws}\,v)_1$ which for each $v\in T$ form a [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15) for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) of the valuation ring and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $=\mathrm{diag}(\varpi_v,1)$ (that is, the representatives lie in the double coset, cover it modulo the subgroup, and are pairwise distinct modulo it); and for every family $\mathrm{zs}$ with $\mathrm{zs}\,v$ the scalar matrix $\varpi_v\cdot 1$ for $v\in T$: there exist continuous $\mathbb{C}$-linear functionals $\mu,\nu$ on $C(X,\mathbb{C})$ with the following two properties.
--
--   (3a) $\mu$ is atom-free in the $T$-coordinates: for every $\tau$ assigning to each place of $K$ a point of $\mathbb{C}\times\mathbb{C}$ and every $\varepsilon>0$ there are sets $U\,v\subseteq\mathbb{C}\times\mathbb{C}$, open and containing $\tau\,v$ for each $v\in T$, such that every $g\in C(X,\mathbb{C})$ with $\lVert g\rVert\le1$ pointwise which vanishes at every $y\in X$ for which $y(w'v)\notin U\,v$ for some $v\in T$ satisfies $\lVert\mu\,g\rVert<\varepsilon$.
--
--   (3b) For all exponent families $\mathrm{ks},\mathrm{js}$, every continuous compactly supported $\varphi:\mathrm{GL}_2(\mathbf{A}_L)\to\mathbb{C}$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds with semi-local factors equal to $\varphi_S\,v$ for $v\notin T$ and, for $v\in T$, to the Hecke-word function
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(\mathrm{ks}\,v)\to\mathrm{Fin}(\mathrm{ns}\,v)}\mathbf{1}_{\mathtt{semiLocalIntegralSet}}\Bigl(\bigl(\mathtt{semiLocalComponent}\,v\,(\mathtt{AdelicDock.localEmbed}\,(\mathrm{ws}\,v)_1\,(\textstyle\prod_m \mathrm{rTs}\,v\,(\iota\,m)\cdot(\mathrm{zs}\,v)^{\mathrm{js}\,v})\bigr)^{-1}x\Bigr),$$
--   and such that $\varphi$ is bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and satisfies `IsArchBiFinite L tysL φ` (namely $g\mapsto\varphi(g^{-1})$ lies in the archimedean cut submodule of type `tysL` and $\varphi$ lies in the dual one); and for every $g\in C(X,\mathbb{C})$ whose values are the word symbol
--   $$g(x)=\prod_{v\in T}\bigl(x(w'v)\bigr)_1^{\mathrm{ks}\,v}\cdot\Bigl(\mathtt{HeckeEigensystem.cNorm}(w'v)^{-1}\bigl(x(w'v)\bigr)_2\Bigr)^{\mathrm{js}\,v}:$$
--   as $R\to+\infty$ the difference
--   $$\int_{\Phi_0}\int_{\Omega_L}\xi_L(z)\cdot\Bigl(\mathtt{AutomorphicForm.lambdaT}\bigr)\bigl(\mathtt{AutomorphicForm.centralScalar}\,z\cdot x\bigr)\,d\nu_{Z_L}(z)\,d(\mathtt{adelicGLHaar})(x)\;-\;\Bigl(V\cdot\!\!\sum_{\Psi}\mathtt{twistedCutTrace}\;+\;\bigl(R\,\nu\,g+\sum_n \mathrm{cs}\,n\cdot g(\mathrm{tabs}\,n)+\mu\,g\bigr)\Bigr)$$
--   tends to $0$, where the pieces are as follows. The truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) is formed with the measure of `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L) (adelicBox L)` on $\mathbf{A}_L$ (Haar measure conditioned on the adelic box), with the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, with height function [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), at truncation parameter $\exp R$, applied to the function $y\mapsto\mathtt{AutomorphicForm.twistedAdelicKernel}\,L\,(\mathtt{sigmaAdelicAct}\,K\,L\,D\,\sigma^{-1})\,\varphi\,x\,y=\sum_{\gamma\in\mathrm{GL}_2(L)}^{\text{finsum}}\varphi(x^{-1}\gamma\,\sigma^{-1}(y))$; it subtracts from this function its constant term on the locus where the adelic height exceeds $\exp R$. The factor $V$ is the real volume $\nu_{Z_L}\bigl(\Omega_L\cap\{z\mid \text{ideleNorm}_L(\det(\mathtt{centralScalar}\,z))\in[\alpha,\beta]\}\bigr)$ regarded as a complex number, and the sum over $\Psi$ runs over the cuspidal classes `cuspClasses L pins ξL N SL`, i.e. over Hecke eigensystems $\Psi$ over $\mathbb{C}$ of level exactly $N$ whose $a$- and $b$-coefficients vanish on $S_L$ and whose isotypic cusp submodule is nonzero, the summand being `twistedCutTrace K L D σ pins ξL N SL Ψ tysL φ` — the trace of the $\sigma$-twisted convolution operator attached to $\varphi$ on the intersection of the isotypic cusp submodule of $\Psi$ with the archimedean cut submodule of type `tysL`, taken to be $0$ if that subspace is not preserved. The remaining bracket is the affine expression in $R$: the linear term $R\cdot\nu\,g$, the atomic sum $\sum_n\mathrm{cs}\,n\,g(\mathrm{tabs}\,n)$ evaluated on the word symbol, and the atom-free term $\mu\,g$.
--
--   The statement is the variant of [`AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub), which it cites, carrying in addition the hypothesis `hSLram` that $S_L$ contain every place of $L$ ramified over $K$; consequently every admissible shift set $T$ consists of places of $K$ unramified in $L/K$.
--
--   This is the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, in asymptotic form and read along Hecke words at two or more shift places: the truncated twisted kernel integral, minus the cuspidal twisted traces, minus an affine expression in the truncation parameter built from an atomic Eisenstein sum and an atom-free functional of the word symbol, tends to $0$. Combined with the affine dependence on $R$ coming from the geometric side it yields an exact spectral identity, and in this form, with the ramified places absorbed into the level set $S_L$, it is used by [`AutomorphicForm.exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram`](thm.html#AutomorphicForm.exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub_unram.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct.RightActions in

theorem
    AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSLram : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
    Filter.Tendsto (fun R : ℝ =>
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φ x y)
            (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                    Ψ ∈ cuspClasses L
                      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                  twistedCutTrace K L D σ
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) +
            ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g)))
      Filter.atTop (nhds 0) := by sorry
