-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_edgeNondegAt_stdEdge_of_isUnit
-- name    : CerednikDrinfeld.FormalOmega.edgeNondegAt_stdEdge_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/8a75520e-d2a4-55fb-a9e4-60eec131026b
-- title:
--   Nondegeneracy of the standard edge at primes containing π
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring (a domain) with fraction field $K$, let $\pi \in \mathcal O$ be irreducible, and let $q$ be a natural number with $\#(\mathcal O/\pi\mathcal O) = q$. Let $g \in \mathrm{GL}_2(K)$ have underlying matrix $\operatorname{diag}(\pi, 1)$. Let $B$ be a commutative $\mathcal O$-algebra and $\xi, \eta \in B$ with $\xi\eta$ equal to the image of $\pi$ in $B$ and with $\xi^{q-1}-1$ and $\eta^{q-1}-1$ units of $B$, and let $\mathfrak p \subset B$ be a prime ideal containing the image of $\pi$. Write $M_0 \subset K^2$ for the standard lattice $\mathcal O^2$ and $e_0, e_1 \in M_0$ for the standard basis vectors $\mathrm{Pi.single}\,i\,1$; let $gM_0$ be its image under $v \mapsto gv$. The assertion is the conjunction of four statements: $gM_0 \subseteq M_0$; $\pi v \in gM_0$ for every $v \in M_0$; for every $v \in M_0$ with $v \notin gM_0$, the element $1 \otimes v$ of $B \otimes_{\mathcal O} M_0$ lies outside $B\cdot(\xi \otimes e_0 + 1 \otimes e_1) + \mathfrak p\,(B \otimes_{\mathcal O} M_0)$; and for every $v' \in gM_0$ which is not of the form $\pi w$ with $w \in M_0$, the element $1 \otimes v'$ of $B \otimes_{\mathcal O} gM_0$ lies outside the sum of $\mathfrak p\,(B \otimes_{\mathcal O} gM_0)$ and the image of $B\cdot(1 \otimes e_0 + \eta \otimes e_1)$ under the $B$-linear isomorphism $B \otimes_{\mathcal O} M_0 \cong B \otimes_{\mathcal O} gM_0$ obtained from $v \mapsto gv$ by base change.
--
--   This is the nondegeneracy condition of the Deligne datum formalism — the two element-wise clauses appearing in the `nondeg` field of `DeligneDatum` — verified at the standard edge $\pi M_0 \subseteq gM_0 \subseteq M_0$ of the Bruhat–Tits tree of $\mathrm{GL}_2(K)$ for the pair of lines cut out by $\xi$ and $\eta$, and stated directly on submodules so that it is available before a Deligne datum has been assembled. It feeds the construction of the Deligne datum whose lines are those of the edge chart, and the admissible-cover statement for special formal schemes in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_edgeNondegAt_stdEdge_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.edgeNondegAt_stdEdge_of_isUnit
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ξ η : B) (hξη : ξ * η = algebraMap 𝒪 B π)
    (hξ : IsUnit (ξ ^ (q - 1) - 1)) (hη : IsUnit (η ^ (q - 1) - 1))
    (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) :
    (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (stdFullLattice (𝒪 := 𝒪) K).1 ∧
    (∀ v : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
      (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) ∧
    (∀ v : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v : Fin 2 → K) ∉ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 →
      (1 : B) ⊗ₜ[𝒪] v ∉
        Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ⊔
          (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)))) ∧
    (∀ v' : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1,
      (¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉
        (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + η ⊗ₜ[𝒪] stdBasisVec K 1}).map
            (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap ⊔
          (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))))) := by sorry
