-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_13
-- name    : BlockSSM.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:06:30.138613+00:00
-- url     : https://prove2.me/theorems/7211b281-9522-4a07-854b-9f55c3d18125
-- title:
--   Theorem 13 — extraspecial groups, $D_b(E_{p,n})\in\{\infty,\,pn\}$
-- statement:
--   Let $p$ be a prime, $n\ge1$, and $E$ an extraspecial group of order $p^{1+2n}$ (its centre, derived subgroup and Frattini subgroup coincide and have order $p$), of either isomorphism type. Then for every block bound $b$, including $b=\infty$,
--   $$
--   D_b(E)=\begin{cases}\infty,& b<p,\\ p\,n,& b\ge p.\end{cases}
--   $$
--
--   The value $pn$ is exponentially smaller than the least faithful degree $p^n$ of $E$ itself, so passing to covers saves exponentially in hidden dimension.
--
--   Differences from the source:
--   - encoding: $E_{p,n}$, "either extraspecial group of order $p^{1+2n}$", either isomorphism type → every group $E$ with $|E|=p^{1+2n}$ satisfying the published `OddOrder.GroupTheory.IsExtraspecial p E` ($p$-group with $Z(E)=[E,E]=\Phi(E)$ of order $p$); reason: these are exactly the extraspecial groups of that order, both types
--   - generalization: the cases $b<p$ and $b\ge p$ for block bounds $b\ge1$, $b=\infty$ included → `if b < p then ⊤ else p * n` for every $b\in$ `ℕ∞`, $b=0$ included; reason: $b=\infty$ falls in the case $b\ge p$ and $\infty$ is `⊤`; the extra instance $b=0$ falls in the case $b<p$ and is true ($D_0(E)=\infty$: irreducible degrees are $\ge1$, so only the zero representation is admissible, which is not faithful on a nontrivial cover); every source instance is a case
--   - encoding: a minimum with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
--   - encoding: finite covers $H$ and representations $V$ in $D_b$ → $H$ in the lowest universe, $V=\mathbb C^d$ (published `BlockSSM.coverDim`); reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 13, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_BlockSSM_coverDim
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **Theorem 13 (extraspecial groups).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 13, p.6 (PDF p.7): "For every prime p,
n ≥ 1, and either isomorphism type, D_b(E_{p,n}) = ∞ if b < p and = pn if b ≥ p. This includes
b = ∞." Here (§6, p.6) "E_{p,n} [is] either extraspecial group of order p^{1+2n}. Its centre, derived
subgroup, and Frattini subgroup agree and have order p."

**Formalization Note.** The theorem is stated for every group `E` of order `p^{1+2n}` that is
extraspecial in the sense of the published `OddOrder.GroupTheory.IsExtraspecial` (a `p`-group with
`Z(E) = [E,E] = Φ(E)` of order `p`), which covers both isomorphism types. The value is the product
`p·n`, not `pⁿ` (`pⁿ` is the least faithful degree of `E` itself). `b : ℕ∞`, so `b = ∞` falls
in the case `b ≥ p`. -/
theorem theorem_13 (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (E : Type u) [Group E]
    (hcard : Nat.card E = p ^ (1 + 2 * n)) (hE : OddOrder.GroupTheory.IsExtraspecial p E)
    (b : ℕ∞) :
    coverDim E b = if b < (p : ℕ∞) then ⊤ else ((p * n : ℕ) : ℕ∞) := by sorry

end BlockSSM.Supplement
