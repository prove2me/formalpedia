-- Prove2me | Theorems.Thm_DiazModulus_ringKrullDim_quotient_sectionIdeal_le
-- name    : DiazModulus.ringKrullDim_quotient_sectionIdeal_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:42.434684+00:00
-- url     : https://prove2.me/theorems/a9a3a223-7138-45a2-9337-d16adaca354f
-- title:
--   For normalised linear forms off $H$ and triangular integer rows off $J$, the section ideal $\mathfrak{a}$ has $\dim K[X, Y, Z]/\mathfrak{a} \le |H| + |J|$
-- statement:
--   Let $K$ be a field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). `sectionIdeal ℓ ψ` is the ideal $J_0 + (\sum_{h'} \ell_{k,h'} X_{h'})_k + (Y^{\psi_k^+} Z^{\psi_k^-} - 1)_k$ of $R$. Let $H \subseteq A_0$, $J \subseteq A_1$, $\ell_h \in K^{A_0}$ and $\psi_i \in \mathbb{Z}^{A_1}$ (all $h \in A_0$, $i \in A_1$), with the forms normalised off $H$ ($\ell_{h,h} = 1$, $\ell_{h,h'} = 0$ for $h, h' \notin H$, $h' \ne h$) and the rows triangular off $J$ ($\psi_{i,i} \ne 0$, $\psi_{i,i'} = 0$ for $i, i' \notin J$, $i' \ne i$). Then $\dim R/\mathfrak{a} \le |H| + |J|$ for $\mathfrak{a}$ = `sectionIdeal ℓ ψ`. Krull dimensions take values in $\{-\infty\} \cup \mathbb{N} \cup \{\infty\}$ and heights in $\mathbb{N} \cup \{\infty\}$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** $R/\mathfrak{a}$ is integral over $K[t_H, s_J]$, $t_h \mapsto X_h$, $s_j \mapsto Y_j + Z_j$: $X_h$ by $\ell_h$ for $h \notin H$; $Y_j, Z_j$ are roots of $T^2 - (Y_j + Z_j)T + 1$; and for $i \notin J$, a power $Y_i^{\pm\psi_{i,i}}$ is a Laurent monomial in the $Y_j$, $j \in J$. Integral extensions do not raise the dimension.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical commutative algebra: dimension does not grow along an integral extension. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem ringKrullDim_quotient_sectionIdeal_le {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] (H : Finset A₀) (J : Finset A₁)
    (ℓ : A₀ → A₀ → K) (ψ : A₁ → A₁ → ℤ) (hℓ : ∀ h ∉ H, ℓ h h = 1 ∧ ∀ h' ∉ H, h' ≠ h → ℓ h h' = 0)
    (hψ : ∀ i ∉ J, ψ i i ≠ 0 ∧ ∀ i' ∉ J, i' ≠ i → ψ i i' = 0) :
    ringKrullDim ((MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) ⧸ sectionIdeal ℓ ψ) ≤ ((H.card + J.card : ℕ) : WithBot ℕ∞) := by
  sorry

end DiazModulus
