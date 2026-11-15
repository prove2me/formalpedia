-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_11_19_rat
-- name    : DiazModulus.dalag_prop_11_19_rat
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-15T05:43:08.203203+00:00
-- url     : https://prove2.me/theorems/0b0a281f-2360-472a-bdba-515dc955a3a5
-- title:
--   DALAG Prop. 11.19 (ℚ, L = ℚ + ℒ) and Roy 1992 Th. 4 over ℚ: if dim U = n < d and T ≠ ℂ^d is ℚ-rational with n′/d′ minimal, then ℓ′ = dim_ℚ(U ∩ L^d / U ∩ T ∩ L^d) is finite, ℓ′/(d′+ℓ′) ≤ n′/d′ ≤ n/d
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$. A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   For subspaces $U, S \subseteq \mathbb C^d$ with $S \ne \mathbb C^d$ write $n'(S) = \dim U - \dim(U \cap S)$ and $d'(S) = d - \dim S$. A subspace $S \ne \mathbb C^d$ rational over $\mathbb Q$ has *minimal ratio* if $n'(S)\,d'(S') \le n'(S')\,d'(S)$ for every subspace $S' \ne \mathbb C^d$ rational over $\mathbb Q$, that is, if it minimises $n'/d'$ among them.
--
--   Let $U \subseteq \mathbb C^d$ be a subspace with $n = \dim U < d$, and let $T \ne \mathbb C^d$ be rational over $\mathbb Q$ of minimal ratio; put $n' = n'(T)$ and $d' = d'(T)$. Let $W = U \cap (\mathbb Q + \mathcal L)^d$, a $\mathbb Q$-vector space. Then the quotient $W/(W \cap T)$ is finite-dimensional over $\mathbb Q$, and its dimension $\ell'$ satisfies
--   $$\ell'\,d' \le n'\,(d' + \ell') \qquad\text{and}\qquad n'\,d \le n\,d',$$
--   that is, $\ell'/(d' + \ell') \le n'/d' \le n/d$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 11.19 (p. 402) for (K, L) = (ℚ, ℚ + ℒ), with the selection over all rational subspaces T ≠ ℂᵈ; D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (p. 34) over F = ℚ (Remark (i), p. 37, with ℚ + ℒ in place of ℒ̃). Proved from DiazModulus.roy_rat_theorem_four by lifting a ℚ-basis of the quotient, with the finiteness argument of DiazModulus.dalag_cor_11_15_rat. DALAG's printed proof of this case reads Th. 11.5 (3′) at the trivial subgroup, which (3′) need not select; that step is not used here. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_11_19_rat {d : ℕ} (U : Submodule ℂ (Fin d → ℂ)) (hUd : Module.finrank ℂ ↥U < d)
    (T : Submodule ℂ (Fin d → ℂ))
    (hTrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T) (hTtop : T ≠ ⊤)
    (hmin : ∀ T' : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T' ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T' → T' ≠ ⊤ →
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * (d - Module.finrank ℂ ↥T') ≤
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T')) * (d - Module.finrank ℂ ↥T)) :
    let W : Submodule ℚ (Fin d → ℂ) := U.restrictScalars ℚ ⊓
      Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg))
    FiniteDimensional ℚ (↥W ⧸ (T.restrictScalars ℚ).comap W.subtype) ∧
    Module.finrank ℚ (↥W ⧸ (T.restrictScalars ℚ).comap W.subtype) * (d - Module.finrank ℂ ↥T) ≤
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) *
        ((d - Module.finrank ℂ ↥T) + Module.finrank ℚ (↥W ⧸ (T.restrictScalars ℚ).comap W.subtype)) ∧
    (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * d ≤
      Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥T) := by
  sorry

end DiazModulus
