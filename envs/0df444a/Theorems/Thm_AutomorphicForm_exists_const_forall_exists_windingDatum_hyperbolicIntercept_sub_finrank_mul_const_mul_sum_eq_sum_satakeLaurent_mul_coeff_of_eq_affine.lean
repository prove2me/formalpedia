-- Prove2me | Theorems.Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
-- name    : AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/084af2b3-6ac0-5ed4-bc63-6faf4e579d44
-- title:
--   A uniform transfer constant for hyperbolic intercepts
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite Galois, $\sigma$ is an automorphism of $L$ over $K$ such that every element of $\mathrm{Gal}(L/K)$ is an integer power of $\sigma^{-1}$ (hypothesis `hgen`), and $[L:K]$ is prime (`hdeg`).
--
--   **Global window and quotient data over $L$.** Reals $\alpha<\beta$ with $0<\alpha$ are fixed. A set $\Phi_L$ of adelic points of $GL_2$ over $L$ is contained in the window $\{g\mid \|\det g\|_L\in[\alpha,\beta]\}$ cut out by the idele norm (`hΦs`) and is a fundamental domain for the image of $GL_2(L)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to that window (`hΦ`). A Haar measure $\nu_{Z_L}$ on the idele units of $L$ is fixed, together with a fundamental domain $\Omega_L$ for the image of $L^\times$ in those units (`hΩL`). Furthermore $D$ is an idele Galois descent datum for $\mathcal{O}_L$, $K$, $L$, that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring of $L$, compatible with the structure map from $L$ and continuous in each component.
--
--   **Place sets.** Finite sets $S_K$ of finite places of $K$ and $S_L$ of finite places of $L$ satisfy: every place of $L$ lying under a place of $S_K$ belongs to $S_L$ (`hSL`); membership in $S_L$ depends only on the place of $K$ below (`hSsat`); and every place of $L$ whose place below is outside $S_K$ has ramification index $1$ (`hS`).
--
--   **The character $\xi_L$.** $\xi_L$ is a homomorphism from the full subgroup of the idele units of $L$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the image of $L^\times$ (`hξt`), taking the same value on $\det(\mathrm{heckeGen}_w)$ and $\det(\mathrm{heckeGen}_{w'})$ whenever $w,w'\notin S_L$ lie over the same place of $K$ (`hξσ`), and invariant under the action of $\sigma^{-1}$ on ideles given by `D.unitsAct` (`hξinv`). An ideal $N$ of $\mathcal{O}_L$ is chosen with all prime divisors in $S_L$ (`hN`), and $\mathrm{tys}_L$ is an archimedean type family for $L$ (a number of types and a choice of archimedean representation types at each infinite place).
--
--   **Test data and a compact parameter box.** Fixed are a function $\varphi_a$ on $GL_2$ of the infinite adeles of $L$, functions $\varphi_S(v)$ on $GL_2(L\otimes_K K_v)$ for the finite places $v$ of $K$, a function $f_{a,K}$ on $GL_2$ of the infinite adeles of $K$ which is an archimedean test factor (a smooth function of the archimedean matrix entries, with compact support; `hfaK`), and functions $f_{S,K}(v)$ on $GL_2(K_v)$ which for $v\in S_K$ are local test functions, i.e. locally constant with compact support (`hfSK`). Moreover $X$ is a compact set (`hXc`) of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$ which contains (`hX`) the set of all $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, the second coordinate equals $\mathrm{N}(w)\cdot\xi_L(\det \mathrm{heckeGen}_w)$, the first coordinate satisfies $\|(x_w)_1\|\le(\mathrm{N}(w)+1)\sqrt{\|\xi_L(\det\mathrm{heckeGen}_w)\|}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   **Data over $K$.** Similarly $\Phi_K$ lies in the determinant-norm window $[\alpha,\beta]$ for $K$ (`hΦKs`) and is a fundamental domain for the image of $GL_2(K)$ with respect to the restricted adelic Haar measure (`hΦK`); $\nu_{Z_K}$ is a Haar measure on the idele units of $K$ and $\Omega_K$ a fundamental domain for the image of $K^\times$ (`hΩK`). $\Xi$ is a finite set of characters of the full subgroup of idele units of $K$ which consists (`hΞ`) exactly of those $\xi$ that are continuous, trivial on the image of $K^\times$, and satisfy $\xi\circ(\text{idelic norm of the base change } K\to L)=\xi_L$; each $\xi\in\Xi$ is unramified outside $S_K$, in the sense that $\xi$ kills the idele attached to any local unit of absolute value $1$ at a place $v\notin S_K$ (`hur`). An ideal $N'$ of $\mathcal{O}_K$ has all prime divisors in $S_K$ (`hN'`), $\mathrm{tys}_K$ is an archimedean type family for $K$, and $c_0$ is a complex number.
--
--   **The geometric comparison hypothesis `hgeo`.** For every finite set $S'\supseteq S_K$ of finite places of $K$ and every pair of functions $\varphi$ on adelic $GL_2$ over $L$ and $f$ on adelic $GL_2$ over $K$ such that: $\varphi$ is continuous with compact support and is unit-factorisable above $S'$ in the sense of `IsUnitFactorizableAbove` for the level subgroup $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, together with archimedean bi-finiteness of type $\mathrm{tys}_L$; $f$ is continuous with compact support, unit-factorisable at $S'$ for $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and archimedean bi-finite of type $\mathrm{tys}_K$; $\varphi$ and $f$ match at $S'$ relative to $\sigma^{-1}$ (`AreMatchingAt`: there are archimedean, finite and semi-local factorisations of $\varphi$ and $f$ whose archimedean parts match and whose local parts match at each place of $S'$); and at every $v\notin S'$ all of whose extensions to $L$ are unramified, the indicator of the semi-local integral set matches the indicator of the local integral set — then
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\bigl(x^{-1}\,\delta\,\sigma^{-1}_D(z\,x)\bigr)\,d\nu_{Z_L}\,d\mu_L = c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\bigl(\mathcal{K}^{\mathrm{cent}}_f(x,zx)+\mathcal{K}^{\mathrm{ell}}_f(x,zx)\bigr)\,d\nu_{Z_K}\,d\mu_K,$$
--   where $z$ is inserted as a central scalar matrix, $\sigma^{-1}_D$ denotes the automorphism of adelic $GL_2$ induced by $D$ at $\sigma^{-1}$, the (finitely supported) sum runs over those $\delta\in GL_2(L)$ whose $\sigma^{-1}$-twisted norm class is the conjugacy class of some $\gamma\in GL_2(K)$ lying in the elliptic or the central cell, and $\mathcal{K}^{\mathrm{cent}}_f$, $\mathcal{K}^{\mathrm{ell}}_f$ are the central and elliptic parts of the adelic kernel of $f$, i.e. the sums of $f(x^{-1}\gamma y)$ over the central and elliptic cells of $GL_2(K)$.
--
--   **Conclusion.** There exists $\lambda\in\mathbb{C}$, $\lambda\ne 0$, with the following two properties.
--
--   (i) If there exist a finite set $S'\supseteq S_K$ and functions $\varphi$, $f$ which are continuous with compact support, unit-factorisable above respectively at $S'$ of the types described above for the levels $\mathrm{levelOne}(N)$ and $\mathrm{principalLevel}(N')$ intersected with the finite-adelic subgroups, matching at $S'$ relative to $\sigma^{-1}$, with the indicator matching condition at the unramified places outside $S'$, and such that
--   $$\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\bigl(\mathcal{K}^{\mathrm{cent}}_f(x,zx)+\mathcal{K}^{\mathrm{ell}}_f(x,zx)\bigr)\,d\nu_{Z_K}\,d\mu_K\ \ne\ 0,$$
--   then $[L:K]\cdot\lambda=c_0$.
--
--   (ii) For every finite set $T$ of finite places of $K$ disjoint from $S_K$ (`hTdisj`) with $|T|\ge 2$ (`hT2`) such that no place of $L$ above a place of $T$ lies in $S_L$ (`hTSL`), and for every choice of the following data: an extension $w_v$ of each place $v$ of $K$ to $L$; a map $v\mapsto w'(v)$ with $w'(v)$ having ideal $\sigma^{-1}\cdot w_v$ for $v\in T$ (`hw'`); elements $\varpi_v$ of the valuation ring of $L_{w_v}$ which for $v\in T$ are irreducible with non-zero image in $L_{w_v}$ (`hϖirr`, `hϖs0`); natural numbers $n_v$ and families $r_{T,v}:\mathrm{Fin}(n_v)\to GL_2(L_{w_v})$ forming, for $v\in T$, a Hecke coset system for the integral subgroup and the element $\mathrm{diag}(\varpi_v,1)$ (`hrTs`: the representatives lie in the double coset, cover it modulo the integral subgroup, and are pairwise inequivalent); elements $z_v\in GL_2(L_{w_v})$ equal for $v\in T$ to the scalar matrix $\varpi_v$ (`hzs`); the corresponding data over $K$, namely uniformisers $\varpi_{K,v}$ (irreducible with non-zero image for $v\in T$), numbers $n_{K,v}$, Hecke coset systems $r_{K,v}$ for $\mathrm{diag}(\varpi_{K,v},1)$, and scalar matrices $z_{K,v}=\varpi_{K,v}$ for $v\in T$; and complex numbers $s(v)$ with $s(v)^2=\xi_L(\det\mathrm{heckeGen}_{w'(v)})$ for $v\in T$ (`hs`) — there exists a winding datum $\mathcal{B}$ of shape $\bigl(r,d,c\bigr)=\bigl(\#\{\text{infinite places of }K\},\,|T|,\,\#\{\text{infinite places of }K\}+|T|\bigr)$ such that the following holds.
--
--   Let $k,j$ be functions from the finite places of $K$ to $\mathbb{N}$, let $\varphi_L$ be continuous with compact support on adelic $GL_2$ over $L$, and let $\varphi_f$ be a function on $GL_2$ of the finite adeles of $L$, subject to: `hSLF`, which asserts that $(\varphi_L,\varphi_a,\varphi_f)$ is a semi-local factorisation over $S_K\cup T$ whose semi-local component at $v\in T$ is
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(k(v))\to\mathrm{Fin}(n_v)}\mathbf{1}_{\text{semi-local integral set}}\Bigl(\bigl(\text{semi-local component at }v\text{ of the local embedding at }w_v\text{ of }\textstyle\prod_m r_{T,v}(\iota(m))\cdot z_v^{\,j(v)}\bigr)^{-1}x\Bigr)$$
--   and $\varphi_S(v)$ at $v\notin T$, the remaining clauses of `IsSemiLocalFactorization` (that $\varphi_a$ is an archimedean test factor, $\varphi_f$ a finite test factor, each prescribed component a semi-local test function, that $\varphi_f(h)$ is the product of the prescribed components over $S_K\cup T$ when all components outside $S_K\cup T$ are integral, that $\varphi_f(h)=0$ when some component outside $S_K\cup T$ fails integrality, and that $\varphi_L=\varphi_a\circ\mathrm{glArch}\cdot\varphi_f\circ\mathrm{glFin}$) being summarised here; `hbi`, that $\varphi_L$ is bi-invariant under $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$; and `harch`, that $\varphi_L$ is archimedean bi-finite of type $\mathrm{tys}_L$. Let furthermore $\mathrm{fam}$ assign to each family $m$ of exponent pairs $(m_v(0),m_v(1))$ indexed by $v\in T$ a function on adelic $GL_2$ over $K$, such that for every $m$ in the slot index set $\mathrm{slotIndex}(w_\bullet,k,j,T)$ (the product over $v\in T$ of the supports of the corresponding slot words) the hypothesis `hfam` holds: $\mathrm{fam}\,m$ is bi-invariant under $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and archimedean bi-finite of type $\mathrm{tys}_K$, $f_{a,K}$ is an archimedean test factor, each $f_{S,K}(v)$ with $v\in S_K$ is a local test function, and there is a finite test factor $ff$ on $GL_2$ of the finite adeles of $K$ with $ff(h)=\prod_{v\in S_K\cup T}\vartheta_v$ evaluated at the $v$-components of $h$ whenever all components of $h$ outside $S_K\cup T$ lie in the local integral sets, where $\vartheta_v$ at $v\in T$ is
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(m_v(0))\to\mathrm{Fin}(n_{K,v})}\mathbf{1}_{\text{local integral set}}\Bigl(\bigl(\textstyle\prod_m r_{K,v}(\iota(m))\cdot z_{K,v}^{\,m_v(1)}\bigr)^{-1}x\Bigr)$$
--   and $\vartheta_v=f_{S,K}(v)$ otherwise, with $ff(h)=0$ when some component outside $S_K\cup T$ fails integrality, and with $\mathrm{fam}\,m\,g=f_{a,K}(\mathrm{glArch}\,g)\cdot ff(\mathrm{glFin}\,g)$; and finally `hmatch`, that $\varphi_L$ and $x\mapsto\sum_m \mathrm{slotFamilyCoeff}(w_\bullet,k,j,T,m)\cdot\mathrm{fam}\,m\,x$ (the sum over the slot index set, with the slot coefficients being the products over $v\in T$ of the slot coefficients) match at $S_K\cup T$ relative to $\sigma^{-1}$.
--
--   Then for all $A_L,B_L\in\mathbb{C}$, all functions $A_K,B_K$ assigning a complex number to each character of the full idele unit subgroup of $K$ and each family of exponent pairs indexed by $T$, and all $R_0\in\mathbb{R}$, the following implication holds. Suppose that for every $R\ge R_0$:
--
--   $\bullet$ the truncated hyperbolic fold over $L$,
--   $$\int_{\mathcal{F}_L(\alpha,\beta)}\int_{\Omega_L}\xi_L(z)\Bigl[\sum_{\delta}\varphi_L\bigl(x^{-1}\delta\,\sigma^{-1}_D(zx)\bigr)-\mathbf{1}_{\{\,\mathrm{adelicHeight}_L>e^{R}\,\}}(zx)\cdot \mathrm{ct}_L(zx)\Bigr]d\nu_{Z_L}\,d\mu_L=R\cdot A_L+B_L,$$
--   where $\mathcal{F}_L(\alpha,\beta)$ is the canonical truncation domain of $L$, the sum runs over those $\delta\in GL_2(L)$ whose $\sigma^{-1}$-twisted norm class is the conjugacy class of a hyperbolic $\gamma\in GL_2(K)$, and $\mathrm{ct}_L$ is the constant term along the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, taken with respect to the measure attached to the production pins of $L$ built from $\Phi_L$, the levels $\mathrm{levelOne}(M)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box of $L$ (namely the adelic additive Haar measure conditioned on that box), of the function $y\mapsto\sum_{\delta}\varphi_L(x^{-1}\delta\,\sigma^{-1}_D(y))$ summed over those $\delta\in GL_2(L)$ with lower-left entry $0$ and $N_{L/K}(\delta_{00}/\delta_{11})\ne 1$; and
--
--   $\bullet$ for every $\xi_K\in\Xi$ and every $m$ in the slot index set, the corresponding truncated hyperbolic integral over $K$,
--   $$\int_{\mathcal{F}_K(\alpha,\beta)}\int_{\Omega_K}\xi_K(z)\Bigl[\mathcal{K}^{\mathrm{hyp}}_{\mathrm{fam}\,m}(x,zx)-\mathbf{1}_{\{\,\mathrm{adelicHeight}_K>e^{R}\,\}}(zx)\cdot \mathrm{ct}_K(zx)\Bigr]d\nu_{Z_K}\,d\mu_K=R\cdot A_K(\xi_K)(m)+B_K(\xi_K)(m),$$
--   where $\mathcal{K}^{\mathrm{hyp}}_{\mathrm{fam}\,m}$ is the hyperbolic part of the adelic kernel of $\mathrm{fam}\,m$ and $\mathrm{ct}_K$ is the analogous constant term, formed with the production pins of $K$ built from $\Phi_K$, the levels $\mathrm{principalLevel}(M)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box of $K$, of $y\mapsto\sum_{\gamma}\mathrm{fam}\,m\,(x^{-1}\gamma y)$ over those $\gamma\in GL_2(K)$ with lower-left entry $0$ and $\gamma_{00}/\gamma_{11}\ne 1$.
--
--   Then the intercepts satisfy
--   $$B_L-[L:K]\,\lambda\sum_{\xi_K\in\Xi}\ \sum_{m}\mathrm{slotFamilyCoeff}(m)\,B_K(\xi_K)(m) =\sum_{n}\Bigl(\prod_{i}\bigl(\sqrt{\mathrm{N}(w'(v_i))}\,s(v_i)\bigr)^{k(v_i)}\ \xi_L\bigl(\det\mathrm{heckeGen}_{w'(v_i)}\bigr)^{j(v_i)}\ \bigl[(T+T^{-1})^{k(v_i)}\bigr]_{n_i}\Bigr)\,\mathcal{B}.\mathrm{coeff}(n),$$
--   where $i$ runs over $\mathrm{Fin}(|T|)$, $v_i$ denotes the $i$-th element of $T$ under the enumeration `T.equivFin`, $n$ runs over all tuples with $n_i\in[-k(v_i),k(v_i)]\cap\mathbb{Z}$, $\bigl[(T+T^{-1})^{k}\bigr]_{n_i}$ is the coefficient of the Laurent polynomial $(T+T^{-1})^{k}$ in degree $n_i$, $\mathrm{N}$ denotes the absolute norm of the corresponding prime ideal, and $\mathcal{B}.\mathrm{coeff}(n)$ is the coefficient of the winding datum at $n$, that is $\sum_{i\in\mathbb{N}}\mathcal{B}.\mathrm{lam}(i)\,\mathcal{B}.\mathrm{fibreCoeff}(i)(n)$.
--
--   This is a step in the comparison of hyperbolic contributions in the twisted and untwisted trace formulae for $GL_2$ over a cyclic extension of prime degree, as used in base change: a single non-zero transfer constant $\lambda$, independent of the auxiliary Hecke place set $T$ and of all uniformiser, coset-representative and word data, is produced, and for each such $T$ the truncated hyperbolic intercepts over $L$ and over $K$ are related, at the constant $[L:K]\lambda$, to the Laurent coefficients of $(T+T^{-1})^{k}$ paired against a winding datum. It is used by [`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindingDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine
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
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    (hξinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (hfaK : IsArchTestFactor K faK)
    (hfSK : ∀ v ∈ SK, IsLocalTestFn K v (fSK v))
    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
      ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous φ ∧ HasCompactSupport φ ∧
        AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧
        Continuous f ∧ HasCompactSupport f ∧
        AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧
        AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧
        (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) →
        (Module.finrank K L : ℂ) * lam = c₀) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K)))
      (hTdisj : Disjoint T SK)
      (hT2 : 2 ≤ T.card)
      (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
      (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
      (hw' : ∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal)
      (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
      (hϖirr : ∀ v ∈ T, Irreducible (ϖs v))
      (hϖs0 : ∀ v ∈ T, algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
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
      (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
      (hϖKirr : ∀ v ∈ T, Irreducible (ϖKs v))
      (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
      (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
      (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
      (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
      (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
      (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
      (s : HeightOneSpectrum (𝓞 K) → ℂ)
      (hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)),
    ∃ (ℬ : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card)),
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
        (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
        (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL)
        (harch : IsArchBiFinite L tysL φL)
        (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ)
        (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
        (hmatch : AreMatchingAt K L σ.symm (SK ∪ T) φL
          (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)),
      ∀ (AL BL : ℂ) (AK BK : (((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → ℂ))) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = (R : ℂ) * AL + BL ∧
          ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * AK ξK m + BK ξK m) →
      (BL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * BK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n) := by sorry
