-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule_principal
-- name    : AutomorphicForm.CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/e225959b-35a1-55bc-bf55-186153c49adc
-- title:
--   Window-independence of K-finite cuspidal constituents at principal level
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}_F$ for its adele ring and $G=\mathrm{GL}_2(\mathbb{A}_F)$. Fix reals $c,u,d_1,d_2$ and a finite set $T\subset G$, with $c>0$, $d_1>0$ and $d_1<d_2$, and put $W=\bigcup_{x\in T}\{g x: g\in\mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every place lies in $[d_1,d_2]$. Assume $W$ covers $G$ modulo the centre: every $g\in G$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in W$ (scalar embedding). Let $P_W$ be the production pins over $W$, i.e. the Borel structure and Haar measure on $G$, domain $W$, centre subgroup $\top$, level groups $N\mapsto$ `principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`, Hecke generators `heckeGen` at the finite places, and the adelic additive Haar measure conditioned on `adelicBox F`; let $\xi$ be a character of the full group of idele units into $\mathbb{C}^\times$, and let $V\subset (G\to\mathbb{C})$ be a $\mathbb{C}$-subspace which is a cuspidal constituent for $(P_W,\xi)$: $V$ lies in `cuspKFiniteSubmodule F P_W ξ`, is stable under right translation by finite-adelic elements and by the determinant-one archimedean row-isometry subgroups and under right convolution with factorizable archimedean-bi-finite test functions, is non-zero, and has no proper non-zero subspace with these stability properties. Assume moreover that for some non-zero ideal $N$ of $\mathcal O_F$ there is a non-zero $\varphi\in V$ with $\varphi(gu)=\varphi(g)$ for all $g\in G$ and all $u$ in the level group at $N$. Then for every further choice of reals $c',u',d_1',d_2'$ with $c'>0$ and $d_1'>0$ and every finite $T'\subset G$ — no covering condition and no inequality between $d_1'$ and $d_2'$ being required — the same space $V$ is contained in `cuspKFiniteSubmodule` for the production pins over $W'=\bigcup_{x\in T'}\{gx:g\in\mathfrak S'\}$, with $\mathfrak S'=$ `centreCutSiegelSet F c' u' d₁' d₂'`, with the same level groups, Hecke generators and box, and the same $\xi$: that is, every vector of $V$ lies in the span of continuous functions all of whose right translates are smooth cuspidal automorphic at the pins over $W'$ and which are cut by some archimedean type family.
--
--   The statement says that membership of the $K$-finite smooth cuspidal space does not depend on the Siegel-type window used to define the pins, once the constituent contains a non-zero vector invariant under a principal congruence level group: growth conditions imposed over one covering window propagate to an arbitrary window. It is used in the identification of cuspidal constituents meeting a principal level, via [`AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre`](thm.html#AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule_principal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hVN : ∃ φ ∈ V, φ ≠ 0 ∧ φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    V ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by sorry
