-- Prove2me | Theorems.Thm_DiazModulus_dalag_cor_11_15_rat
-- name    : DiazModulus.dalag_cor_11_15_rat
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:20.64722+00:00
-- url     : https://prove2.me/theorems/ef098be8-01c6-42f9-b3ed-775d006a6f48
-- title:
--   DALAG Cor. 11.15 for (ℚ, ℚ + ℒ): if V ⊆ ℂᵈ meets ℚᵈ only in 0, then dim_ℚ(V ∩ (ℚ + ℒ)ᵈ) ≤ Ψ(dim V, dₘᵢₙ), with DALAG's table Ψ and dₘᵢₙ the least dimension of a rational S ⊇ V
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). Write $\mathbb Q + \mathcal L$ for the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$; it consists of the numbers $q + \lambda$ with $q \in \mathbb Q$ and $\lambda \in \mathcal L$. A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   DALAG's function $\Psi$ is given by a table (DALAG, §11.5, p. 394). Here, for natural numbers $a, b$, $\Psi(a, b)$ is defined by the following cases, taken in this order: $\Psi(a, b) = 0$ if $a = 0$; else $\Psi(a, b) = 1$ if $a = 1$ and $b \ge 3$; else $a(a - 1) + 1$ if $a \ge 2$ and $a + 3 \le b$; else $a(a - 1) + 2$ if $a \ge 2$ and $a + 2 = b$; else $a(a + 1)$ if $a + 1 = b$; and $0$ in every remaining case (these are $a \ge 1$ with $b \le a$, outside the table). For $0 < a < b$ the four middle cases are the four rows of the printed table, and $\Psi(0, b) = 0$ for every $b$.
--
--   Let $V \subseteq \mathbb C^d$ be a subspace that contains no non-zero rational vector, and let $S_0 \supseteq V$ be a subspace rational over $\mathbb Q$ of least dimension among the subspaces rational over $\mathbb Q$ that contain $V$; write $d_{\min} = \dim S_0$. Then: if $\dim V > 0$, then $\dim V < d_{\min}$; $V \cap (\mathbb Q + \mathcal L)^d$ is a finite-dimensional $\mathbb Q$-vector space; and
--   $$\dim_{\mathbb Q}\big(V \cap (\mathbb Q + \mathcal L)^d\big) \le \Psi(\dim V, d_{\min}).$$
--   For $\dim V = 0$ the bound is $\Psi(0, d_{\min}) = 0$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.15 (p. 398), for (K, L) = (ℚ, ℚ + ℒ), with DALAG's bound Ψ(dim V, d_min), and Ψ(0, b) = 0 for every b as in DiazModulus.dalag_cor_11_15_psi. The proof follows Roy's route over ℚ: D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 5 (p. 39) with his Remark (i) (p. 37), here DiazModulus.roy_rat_theorem_five, and Roy's Lemma (p. 40) through DiazModulus.dalag_psi_floor_roy_phi. DALAG proves the corollary (p. 403) from Prop. 11.19 (p. 402), whose printed proof has a gap in this case (Th. 11.5 (3′) need not select the trivial subgroup); Prop. 11.19 is not used here. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_cor_11_15_rat {d : ℕ} (V S₀ : Submodule ℂ (Fin d → ℂ))
    (hVQ : ∀ v ∈ V, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0)
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S₀)
    (hVS₀ : V ≤ S₀)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T → V ≤ T →
        Module.finrank ℂ ↥S₀ ≤ Module.finrank ℂ ↥T) :
    let Ψ : ℕ → ℕ → ℕ := fun a b =>
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0
    (0 < Module.finrank ℂ ↥V → Module.finrank ℂ ↥V < Module.finrank ℂ ↥S₀) ∧
    FiniteDimensional ℚ ↥(V.restrictScalars ℚ ⊓
        Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg))) ∧
    Module.finrank ℚ ↥(V.restrictScalars ℚ ⊓
        Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg))) ≤
      Ψ (Module.finrank ℂ ↥V) (Module.finrank ℂ ↥S₀) := by
  sorry

end DiazModulus
