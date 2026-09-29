-- Prove2me | Theorems.Thm_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
-- name    : CerednikDrinfeld.levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/430e43b8-2255-5c10-b19c-2cc48b8368e3
-- title:
--   Oriented level-ℓ Hecke set is one double coset of ̂ R^×
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a prime such that [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q'`](def/QuaternionAlgebra_EichlerOrder.html#L87) holds, i.e. $a<0$, $b<0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q'$ lies in $v$. Let $R,\Lambda$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ and $N$ a nonzero squarefree natural number such that $R$ is an Eichler order of level $N$ (there are maximal orders $\Lambda_1,\Lambda_2$ with $R=\Lambda_1\sqcap\Lambda_2$ and relative index $[\Lambda_1:R]=N$), $\Lambda$ is a maximal order (an order, i.e. containing $1$, multiplicatively closed, finitely generated and $\mathbb{Q}$-spanning, and maximal among orders), $R\le\Lambda$ and $q'\nmid N$. Let $\ell$ be a prime dividing $N$ and write $\hat{R}$, $\hat{\Lambda}$ for the finite adelic boxes [`Submodule.finiteAdeleBox`](def/Submodule_FiniteAdeleBox.html#L14). Put $\mathcal{U}=$ `levelHeckeUSet Λ R ℓ`, the set of units $h$ of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},\mathrm{fin}}$ with $h\in\hat R$, $\ell h^{-1}\in\hat R$, $h^{-1}\notin\hat R$, $\ell^{-1}h\notin\hat R$, $\mathbb{H}\cap h\hat R h^{-1}\neq R$ and $R\not\le\mathbb{H}\cap h\hat\Lambda h^{-1}$. Then for any $g\in\mathcal{U}$ one has $\mathcal{U}=UgU=\{u g u' : u,u'\in U\}$, where $U=$ [`Submodule.finiteIdeleStabilizer R`](def/Submodule_FiniteAdeleBox.html#L26) is the group of units stabilising $\hat R$ pointwise-setwise.
--
--   This is the statement, going back to Eichler and used in Hijikata's trace computations, that at a prime $\ell$ dividing the squarefree level the $\Lambda$-oriented Hecke set defining $U_\ell$ on the idelic class set of an Eichler order is a single double coset of $\hat R^\times$. It underlies the Čerednik–Drinfeld class-set graph constructions, being used to identify the meet order attached to a diagonal idèle, to produce explicit representatives of the double coset, and to compare the Hecke action with the class-set Hecke matrix.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (hN : Squarefree N)
    (hR : QuaternionAlgebra.IsEichlerOrder R N) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (hq'N : ¬ q' ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hg : g ∈ CerednikDrinfeld.levelHeckeUSet Λ R ℓ) :
    CerednikDrinfeld.levelHeckeUSet Λ R ℓ =
      DoubleCoset.doubleCoset g (Submodule.finiteIdeleStabilizer R : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
        (Submodule.finiteIdeleStabilizer R : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by sorry
