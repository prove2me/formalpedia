-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq
-- name    : AutomorphicForm.exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/267cc245-4b61-5d00-a370-4567118d0ad7
-- title:
--   Hecke word comparison of twisted and untwisted cut traces
-- statement:
--   **Setting.** Let $K$ and $L$ be number fields with $L/K$ finite and Galois, and let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma^{-1}$ (`hgen`); the degree $[L:K]$ is assumed to be a prime number (`hdeg`). Let $0 < \alpha < \beta$ be real numbers. Let $D$ be an [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28): a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$, compatible with the structural map $L \to \mathbb{A}_L$ and continuous for each automorphism. Throughout, $\mathrm{GL}_2(\mathbb{A}_F)$ carries the Borel structure and the Haar measure `adelicGLHaar`, and $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$ is the map `globalPoints`, while `centralScalar` sends an idele $z$ to the scalar matrix $z \cdot 1$.
--
--   **Fundamental domains and central measures.** The set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ is contained in the slab $\{g : \|\det g\|_L \in [\alpha,\beta]\}$, where $\|\cdot\|_L$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) (`hΦs`), and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic Haar measure restricted to that slab (`hΦ`). The idele group $\mathbb{A}_L^\times$ carries a Borel measurable structure, $\nu_{Z,L}$ is a Haar measure on it and $\Omega_L$ a fundamental domain for the image of $L^\times$ (`hΩL`). The data $\Phi_K$, `hΦKs`, `hΦK`, $\nu_{Z,K}$, $\Omega_K$, `hΩK` are the exact analogues for $K$.
--
--   **Places and levels.** $S_K$ and $S_L$ are finite sets of height-one primes of $\mathcal{O}_K$ and $\mathcal{O}_L$ with: every $w$ lying above a prime of $S_K$ belongs to $S_L$ (`hSL`); membership of $w$ in $S_L$ depends only on the prime of $K$ below $w$ (`hSsat`); every $w$ whose prime below lies outside $S_K$ has ramification index $1$ (`hS`). Moreover $N$ is an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`), and $N'$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN'`).
--
--   **Characters.** $\xi_L$ is a homomorphism from the top subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $L^\times$ (`hξt`), and takes the same value on $\det(\mathrm{heckeGen}_L(w))$ and $\det(\mathrm{heckeGen}_L(w'))$ whenever $w, w' \notin S_L$ lie above the same prime of $K$ (`hξσ`). $\Xi$ is a finite set of homomorphisms from the top subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ characterised by `hΞ`: a character $\xi$ belongs to $\Xi$ exactly when it is continuous, trivial on the image of $K^\times$, and satisfies $\xi \circ \mathcal{N} = \xi_L$, where $\mathcal{N}$ is the idelic norm attached to `genuineBaseChange K L`.
--
--   **Test functions, components and matching.** $\mathrm{tys}_L$ and $\mathrm{tys}_K$ are archimedean type families (for each infinite place, a finite list of representations of the local row-isometry group). The function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ is continuous with compact support and satisfies `IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK`, i.e. it is unit-factorizable above $S_K$ for the level subgroup cut out by $N$ intersected with the kernel of the archimedean projection, and is archimedean bi-finite of type $\mathrm{tys}_L$ (`hφ`, `hφc`, `hφt`). The function $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ is continuous with compact support and satisfies `IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK` (`hf`, `hfc`, `hft`). Components are given: $\varphi_\infty$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, a family $\varphi_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$, $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles of $K$, and a family $f_S(v)$ on $\mathrm{GL}_2(K_v)$. These satisfy: archimedean matching of $(\varphi_\infty, f_\infty)$ relative to $\sigma^{-1}$ (`harch`); local matching of $(\varphi_S(v), f_S(v))$ relative to $\sigma^{-1}$ for every $v \in S_K$ (`hloc`); existence of a finite-adelic factor $\varphi_f$ making $(\varphi, \varphi_\infty, \varphi_f, \varphi_S)$ a semi-local factorisation over $S_K$ (`hφfac`); and existence of $f_f$ making $(f, f_\infty, f_f, f_S)$ a unit factorisation over $S_K$ (`hffac`).
--
--   **Geometric comparison.** A complex constant $c_0$ is given together with the hypothesis `hgeo`: for every finite set $S' \supseteq S_K$ of primes of $K$ and every pair of functions — a continuous compactly supported $\varphi'$ on $\mathrm{GL}_2(\mathbb{A}_L)$ unit-factorizable above $S'$ of type $\mathrm{tys}_L$ for the level $N$, and a continuous compactly supported $f'$ on $\mathrm{GL}_2(\mathbb{A}_K)$ unit-factorizable at $S'$ of type $\mathrm{tys}_K$ for the principal level $N'$ — which match at $S'$ relative to $\sigma^{-1}$ and for which, at every $v \notin S'$ all of whose extensions to $L$ are unramified, the indicator of the semi-local integral set matches the indicator of the local integral set, one has
--   $$\int_{\Phi_L}\int_{\Omega_L} \xi_L(z)\, \sum_{\delta} \varphi'\bigl(x^{-1}\,\delta\, \sigma^{-1}_{\mathbb{A}}(z\,x)\bigr)\, d\nu_{Z,L}\, d\mu_L = c_0 \sum_{\xi_K \in \Xi} \int_{\Phi_K}\int_{\Omega_K} \xi_K(z)\bigl(K^{\mathrm{cent}}_f(x, z x) + K^{\mathrm{ell}}_f(x, z x)\bigr) d\nu_{Z,K}\, d\mu_K ,$$
--   where the inner finite sum runs over those $\delta \in \mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class has norm class equal to the conjugacy class of some $\gamma \in \mathrm{GL}_2(K)$ which is either elliptic (its characteristic polynomial has no root in $K$) or central (a scalar matrix), $\sigma^{-1}_{\mathbb{A}}$ denotes the entrywise action of $D$ at $\sigma^{-1}$, and $K^{\mathrm{cent}}_f$, $K^{\mathrm{ell}}_f$ are the central and elliptic parts of the adelic kernel, $\sum_{\gamma \text{ central}} f(x^{-1}\gamma y)$ and $\sum_{\gamma \text{ elliptic}} f(x^{-1}\gamma y)$.
--
--   **Siegel covering data for $K$.** Real numbers $c_K, u_K, d_{1,K}, d_{2,K}$ with $0 < c_K$, $0 < d_{1,K} < d_{2,K}$ (`hcK`, `hd₁K`, `hdK`) and a finite set $T_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ are given such that the union of the right translates $(\cdot\, x)$ of the centre-cut Siegel set with parameters $c_K, u_K, d_{1,K}, d_{2,K}$, over $x \in T_K$, covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo global points and the centre (`hcovK`).
--
--   **Fundamental-lemma hypotheses.** Three hypotheses are assumed at primes $v \notin S_K$. `hFLu`: if every prime of $L$ above $v$ is unramified, then the indicator of the semi-local integral set of $L \otimes_K K_v$ matches the indicator of the integral set of $\mathrm{GL}_2(K_v)$, relative to $\sigma^{-1}$. `hFLs` (split case): for every $K_v$-algebra isomorphism $e : L \otimes_K K_v \cong (\mathrm{Fin}\,[L:K] \to K_v)$, every index $i_0$, every subgroup $U$ equal to the image of $\mathrm{GL}_2(\mathcal{O}_v)$ in $\mathrm{GL}_2(K_v)$, and every element $f_1$ of the Hecke algebra of $U$ over $\mathbb{C}$, the function sending $g$ to $f_1$ evaluated at the $i_0$-th component of $e(g)$ times the indicator of the set of $h$ whose components at all $i \neq i_0$ lie in $U$ matches $f_1$. `hFLi` (inert case): for every extension $w$ of $v$ to $L$ with ramification index $1$, every $K_v$-algebra isomorphism $e : L \otimes_K K_v \cong L_w$, irreducible uniformisers $\varpi_K \in \mathcal{O}_v$ and $\varpi_L \in \mathcal{O}_w$ with nonzero images, the integral subgroups $U_K \subseteq \mathrm{GL}_2(K_v)$ and $U_L \subseteq \mathrm{GL}_2(L_w)$, elements $T, E$ of the Hecke algebra of $U_K$ with $T$ the indicator of the double coset of $\mathrm{diag}(\varpi_K, 1)$ and $E$ equal to $\mathrm{Nm}(v)$ times the indicator of $\varpi_K U_K$, the analogous elements $T', E'$ for $U_L$ and $\varpi_L$ with $\mathrm{Nm}(w)$, and every sequence $p$ in the Hecke algebra of $U_K$ with $p_0 = 2$, $p_1 = T$ and $p_{k+2} = T p_{k+1} - E p_k$: there is a $\mathbb{C}$-algebra homomorphism $b$ from the Hecke algebra of $U_L$ to that of $U_K$ with $b(T') = p_{[L:K]}$, $b(E') = E^{[L:K]}$, and such that for every $\phi$ in the Hecke algebra of $U_L$ the function $g \mapsto \phi(e(g))$ matches $b(\phi)$ relative to $\sigma^{-1}$.
--
--   **Compact sets of tables.** $X$ is a compact set of functions $w \mapsto (x_w^{(1)}, x_w^{(2)}) \in \mathbb{C}\times\mathbb{C}$ on the primes of $\mathcal{O}_L$ which contains (`hX`) the box of all $x$ with $x_w = 0$ for $w \in S_L$ and, for $w \notin S_L$: $x_w^{(2)} = \mathrm{Nm}(w)\,\xi_L(\det \mathrm{heckeGen}_L(w))$, $\|x_w^{(1)}\| \le (\mathrm{Nm}(w)+1)\sqrt{\|\xi_L(\det \mathrm{heckeGen}_L(w))\|}$, and $\overline{x_w^{(1)}} = \overline{x_w^{(2)}}\,\|x_w^{(2)}\|^{-1} x_w^{(1)}$. For each character $\xi_K \in \Xi$ a set $X_K(\xi_K)$ of tables over $K$ is given which is compact (`hXKc`), contains the corresponding box over $K$ (`hXKbox`), and whose formal base change lands in $X$: for $x \in X_K(\xi_K)$ the table $w \mapsto (\mathrm{satakePow}_{f(w|v)}(x_v^{(1)}, x_v^{(2)}),\, (x_v^{(2)})^{f(w|v)})$, with $v$ the prime below $w$ and $f(w|v)$ the inertia degree, lies in $X$ (`hXK`).
--
--   **Conclusion.** There exists $\lambda \in \mathbb{C}$ with the following three properties.
--
--   (1) $\lambda \neq 0$.
--
--   (2) If there exist a finite set $S' \supseteq S_K$ and functions $\varphi'$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $f'$ on $\mathrm{GL}_2(\mathbb{A}_K)$ such that $\varphi'$ is continuous with compact support and unit-factorizable above $S'$ of type $\mathrm{tys}_L$ for the level $N$, $f'$ is continuous with compact support and unit-factorizable at $S'$ of type $\mathrm{tys}_K$ for the principal level $N'$, the pair matches at $S'$ relative to $\sigma^{-1}$, at every $v \notin S'$ with all extensions unramified the indicators of the semi-local and local integral sets match, and
--   $$\sum_{\xi_K \in \Xi}\int_{\Phi_K}\int_{\Omega_K} \xi_K(z)\bigl(K^{\mathrm{cent}}_{f'}(x, z x) + K^{\mathrm{ell}}_{f'}(x, z x)\bigr) d\nu_{Z,K}\, d\mu_K \neq 0,$$
--   then $[L:K]\,\lambda = c_0$.
--
--   (3) There exist a sequence of tables $E : \mathbb{N} \to (\text{primes of } \mathcal{O}_L \to \mathbb{C}\times\mathbb{C})$ with $E_n \in X$ for all $n$, and complex numbers $e_n$ with $\sum_n \|e_n\| < \infty$, such that:
--
--   (3a) for every $n$ with $e_n \neq 0$: first, $E_n$ is constant on fibres of $L/K$ off $S_L$, that is $E_n(w) = E_n(w')$ whenever $w, w' \notin S_L$ lie above the same prime of $K$; and second, off $S_L$ the table $E_n$ is Eisenstein, either over $L$ or by base change from $K$ — either there are a nonzero ideal $M$ of $\mathcal{O}_L$ and two continuous characters $\chi_1, \chi_2$ of $\mathbb{A}_L^\times$ trivial on $L^\times$ with $E_n(w) = (a_w, b_w)$ for every $w \notin S_L$, where $(a, b)$ is the Eisenstein eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M _ χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132) (so $a_w = \chi_1(\varpi_w) + \chi_2(\varpi_w)$ and $b_w = \chi_1(\varpi_w)\chi_2(\varpi_w)$ for the uniformiser idele at $w$), or there are a nonzero ideal $M$ of $\mathcal{O}_K$ and continuous characters $\chi_1, \chi_2$ of $\mathbb{A}_K^\times$ trivial on $K^\times$ and unramified at every $v \notin S_K$ such that $E_n(w)$ equals, for every $w \notin S_L$, the pair of $w$-th coefficients of the formal base change to $L$ of the Eisenstein eigensystem over $K$ attached to $M, \chi_1, \chi_2$;
--
--   (3b) for every finite set $T$ of primes of $K$ disjoint from $S_K$ with $\#T \ge 2$ such that every prime of $L$ above a member of $T$ lies outside $S_L$, every family $\mathrm{ws}$ assigning to each prime $v$ of $K$ an extension of $v$ to $L$, and every map $w'$ from primes of $K$ to primes of $L$ with $(w'(v))$ the ideal $\sigma^{-1}\cdot \mathrm{ws}(v)$ for $v \in T$, there exists a continuous $\mathbb{C}$-linear functional $\Lambda$ on $C(X, \mathbb{C})$ such that:
--
--   (i) *(no atomic mass)* for every table $\tau$ over $K$ and every $\varepsilon > 0$ there is a family $U$ of subsets of $\mathbb{C}\times\mathbb{C}$ with $U(v)$ open and containing $\tau(v)$ for each $v \in T$, such that every $g \in C(X,\mathbb{C})$ which vanishes at every $y \in X$ for which $y(w'(v)) \notin U(v)$ for some $v \in T$, and satisfies $\|g(y)\| \le 1$ everywhere, has $\|\Lambda g\| < \varepsilon$;
--
--   (ii) *(word identity)* for all exponent families $k, j : (\text{primes of }\mathcal{O}_K) \to \mathbb{N}$ and every $g \in C(X,\mathbb{C})$ given by the monomial $g(x) = \prod_{v \in T} (x(w'(v))^{(1)})^{k_v}\,(\mathrm{Nm}(w'(v))^{-1} x(w'(v))^{(2)})^{j_v}$,
--   $$\mathrm{vol}_L \sum_{\Psi} \Bigl(\prod_{v \in T} \Psi.a(w'(v))^{k_v}\bigl(\mathrm{Nm}(w'(v))^{-1}\Psi.b(w'(v))\bigr)^{j_v}\Bigr)\,\mathrm{tCT}(\Psi) \;-\; [L:K]\,\lambda\,\mathrm{vol}_K \sum_{\xi_K \in \Xi}\sum_{\pi}\Bigl(\prod_{v \in T} \mathrm{bc}(\pi).a(w'(v))^{k_v}\bigl(\mathrm{Nm}(w'(v))^{-1}\mathrm{bc}(\pi).b(w'(v))\bigr)^{j_v}\Bigr)\,\mathrm{CT}(\pi) \;+\; \sum_n e_n\, g(E_n) \;=\; \Lambda g .$$
--   Here $\mathrm{vol}_L$ is the real number $\nu_{Z,L}\bigl(\Omega_L \cap \{z : \|\det(z\cdot 1)\|_L \in [\alpha,\beta]\}\bigr)$ viewed in $\mathbb{C}$ and $\mathrm{vol}_K$ its analogue for $K$; the first sum runs over the cusp classes $\Psi$ of $L$ for the pins `productionPinsOf L ΦL` with level family $M \mapsto \mathrm{levelOne}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}(L)$, Hecke generators $\mathrm{heckeGen}_L$ and box `adelicBox L`, with character $\xi_L$, level $N$ and set $S_L$ (that is, Hecke eigensystems of level exactly $N$ vanishing at the places of $S_L$ whose isotypic cusp submodule is nonzero), and $\mathrm{tCT}(\Psi)$ is the $\sigma$-twisted cut trace `twistedCutTrace K L D σ` of $\varphi$ on the intersection of that isotypic cusp submodule with the archimedean cut submodule of type $\mathrm{tys}_L$; the second sum runs over the cusp classes $\pi$ of $K$ for the pins built from the union of the translates $\bigcup_{x \in T_K}(\cdot\, x)$ of the centre-cut Siegel set, the level family $M \mapsto \mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}(K)$, the generators $\mathrm{heckeGen}_K$ and the box `adelicBox K`, with character $\xi_K$, level $N'$ and set $S_K$, $\mathrm{bc}(\pi)$ denotes the formal base change `formalBaseChange K L π`, and $\mathrm{CT}(\pi)$ is the cut trace of $f$ on the corresponding space; both spectral sums are unconditional sums over the respective class sets.
--
--   This is the assembly step of the spectral side of cyclic base change for $\mathrm{GL}_2$ in prime degree: the insertion of Hecke words $T_{w}^{k}z_{w}^{j}$ at the places of $T$ turns the comparison of twisted and untwisted cut traces into an identity of monomial moments of Satake tables, modulo an absolutely summable family of Eisenstein atoms and a functional with no atomic mass in the variables at $T$; the slope constant is recorded as $[L:K]\lambda$, pinned to $c_0$ whenever the untwisted geometric side does not vanish. It is used by [`AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_docks_ed2`](thm.html#AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_docks_ed2) to obtain the fibrewise equality of twisted and untwisted traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_atoms_forall_exists_noAtomicMass_heckeWordSum_twistedCutTrace_sub_finrank_mul_const_mul_heckeWordSum_cutTrace_eq
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f)

    (harch : AreMatchingArch K L σ.symm φa faK)
    (hloc : ∀ v ∈ SK, AreMatchingLocal K L v σ.symm (φS v) (fSK v))
    (hφfac : ∃ φf, IsSemiLocalFactorization K L SK φ φa φf φS)
    (hffac : ∃ ff, IsUnitFactorization K SK f faK ff fSK)
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

    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))

    (hFLu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
      AreMatchingLocal K L v σ.symm ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (hFLs : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      ∀ (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
          (Fin (Module.finrank K L) → v.adicCompletion K))
        (i₀ : Fin (Module.finrank K L)) (U : Subgroup (GL (Fin 2) (v.adicCompletion K))),
        U = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        ∀ f₁ : HeckePair.HeckeAlgebra U ℂ,
          AreMatchingLocal K L v σ.symm
            (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ)
                  (Matrix.GeneralLinearGroup.map
                    ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i₀).comp
                      e.toAlgHom).toRingHom g) *
                ({h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
                    ∀ i : Fin (Module.finrank K L), i ≠ i₀ →
                      Matrix.GeneralLinearGroup.map
                          ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i).comp
                            e.toAlgHom).toRingHom h ∈ U}.indicator (fun _ => (1 : ℂ)) g))
            (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hFLi : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → ∀ (w : v.Extension (𝓞 L)),
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1 →
      ∀ (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
        (ϖK : v.adicCompletionIntegers K), Irreducible ϖK →
        ∀ (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
          (ϖL : w.1.adicCompletionIntegers L), Irreducible ϖL →
        ∀ (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
          (UK : Subgroup (GL (Fin 2) (v.adicCompletion K))),
          UK = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        ∀ (UL : Subgroup (GL (Fin 2) (w.1.adicCompletion L))),
          UL = LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) →
        ∀ (TK EK : HeckePair.HeckeAlgebra UK ℂ),
          (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
            (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator (fun _ => (1 : ℂ)) →
          (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
            (Ideal.absNorm v.asIdeal : ℂ) •
              ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ UK,
                  (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                      (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator
                fun _ => (1 : ℂ)) →
        ∀ (TL EL : HeckePair.HeckeAlgebra UL ℂ),
          (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
            (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator (fun _ => (1 : ℂ)) →
          (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
            (Ideal.absNorm w.1.asIdeal : ℂ) •
              ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ UL,
                  (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
                    algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                      (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator
                fun _ => (1 : ℂ)) →
        ∀ (p : ℕ → HeckePair.HeckeAlgebra UK ℂ), p 0 = 2 → p 1 = TK →
          (∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) →
          ∃ b : HeckePair.HeckeAlgebra UL ℂ →ₐ[ℂ] HeckePair.HeckeAlgebra UK ℂ,
            b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
              ∀ φ : HeckePair.HeckeAlgebra UL ℂ,
                AreMatchingLocal K L v σ.symm
                  (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
                    (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
                      (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
                  (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ))

    (XK : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ))
    (hXKc : ∀ ξK ∈ Ξ, IsCompact (XK ξK))
    (hXKbox : ∀ ξK ∈ Ξ,
      {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
            (∀ v ∈ SK, x v = 0) ∧
            ∀ v ∉ SK,
              (x v).2 = HeckeEigensystem.cNorm v *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
              ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
                  Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                    ℂˣ) : ℂ)‖ ∧
              conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ XK ξK)
    (hXK : ∀ ξK ∈ Ξ, ∀ x ∈ XK ξK,
      (fun w : HeightOneSpectrum (𝓞 L) =>
        (satakePow ((HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)
            (x (HeightOneSpectrum.under (𝓞 K) w)).1 (x (HeightOneSpectrum.under (𝓞 K) w)).2,
          (x (HeightOneSpectrum.under (𝓞 K) w)).2 ^
            (HeightOneSpectrum.under (𝓞 K) w).asIdeal.inertiaDeg' w.asIdeal)) ∈ X) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧ ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ ∧ HasCompactSupport φ ∧ AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧ Continuous f ∧ HasCompactSupport f ∧ AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧ AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) → AutomorphicForm.AreMatchingLocal K L v σ.symm ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧ (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) + AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) → (Module.finrank K L : ℂ) * lam = c₀) ∧
    ∃ (E : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hEX : ∀ n, E n ∈ X) (e : ℕ → ℂ),
    (Summable fun n => ‖e n‖) ∧
    (∀ n, e n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → E n w = E n w') ∧
      ((∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
              χ₂ z = 1) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            E n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
              (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∨
       (∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₁ z = 1) ∧
          (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
          (∀ z : (AdeleRing (𝓞 K) K)ˣ,
            z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
              χ₂ z = 1) ∧
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
            NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
            E n w =
              ((formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).a w,
                (formalBaseChange K L (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂)).b w)))) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (g : C(X, ℂ)),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
            (∑' Ψ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ cuspClasses L
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
              (∏ v ∈ T, (Ψ.1.a (w' v)) ^ ks v * ((HeckeEigensystem.cNorm (w' v))⁻¹ * Ψ.1.b (w' v)) ^ js v) *
                twistedCutTrace K L D σ
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) -
          (Module.finrank K L : ℂ) * lam * ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
            (∑ ξK ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ // π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK},
              (∏ v ∈ T, ((formalBaseChange K L π.1).a (w' v)) ^ ks v *
                  ((HeckeEigensystem.cNorm (w' v))⁻¹ * (formalBaseChange K L π.1).b (w' v)) ^ js v) *
                cutTrace K
                  (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π.1 tysK f hf hfc) +
          (∑' n, e n * g ⟨E n, hEX n⟩) = Λ g := by sorry
