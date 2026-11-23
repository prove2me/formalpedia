-- Prove2me | Theorems.Thm_Castro2006_classification
-- name    : Castro2006.classification
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:43:10.277009+00:00
-- url     : https://prove2.me/theorems/dbedf049-6eed-42d2-9532-1cfec56fc6de
-- title:
--   Classification of $p$-groups with a cyclic subgroup of index $p$ (Teorema 4.5.1)
-- statement:
--   Let $p$ be prime and $G$ a group of order $p^{n+1}$ containing a cyclic subgroup $K$ of index $p$. Then, up to isomorphism, $G$ is one of: $\mathbb{Z}_{p^{n+1}}$ ($n\ge0$); $\mathbb{Z}_{p^n}\times\mathbb{Z}_p$ ($n\ge1$); $\mathbb{Z}_{p^n}\rtimes\mathbb{Z}_p$ with the generator acting by multiplication by $1+p^{n-1}$ ($n\ge2$); and, when $p=2$, additionally the dihedral group $D_{2\cdot2^n}$ ($n\ge3$), the generalized quaternion group $Q_{4\cdot2^{n-1}}$ ($n\ge2$), and $\mathbb{Z}_{2^n}\rtimes\mathbb{Z}_2$ with the generator acting by $-1+2^{n-1}$ ($n\ge3$).
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib
import Definitions.Def_Castro2006_classDefs
open CategoryTheory

namespace Castro2006
theorem classification {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hcard : Fintype.card G = p ^ (n + 1))
    (K : Subgroup G) (hKcyc : IsCyclic K) (hKidx : K.index = p) :
    Nonempty (G ≃* Multiplicative (ZMod (p ^ (n + 1)))) ∨
    (1 ≤ n ∧ Nonempty (G ≃* Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod p))) ∨
    (2 ≤ n ∧ ∃ φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ n))),
      Castro2006.IsModularAction p n φ ∧
      Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod (p ^ n))) (Multiplicative (ZMod p)) φ)) ∨
    (p = 2 ∧ ((3 ≤ n ∧ Nonempty (G ≃* DihedralGroup (2 ^ n))) ∨
      (2 ≤ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ (n - 1)))) ∨
      (3 ≤ n ∧ ∃ φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod (2 ^ n))),
        Castro2006.IsSemidihedralAction n φ ∧
        Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod (2 ^ n))) (Multiplicative (ZMod 2)) φ)))) := by sorry
end Castro2006
