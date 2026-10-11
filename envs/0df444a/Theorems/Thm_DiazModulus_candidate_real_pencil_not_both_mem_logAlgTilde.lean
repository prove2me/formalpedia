-- Prove2me | Theorems.Thm_DiazModulus_candidate_real_pencil_not_both_mem_logAlgTilde
-- name    : DiazModulus.candidate_real_pencil_not_both_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:03:17.539276+00:00
-- url     : https://prove2.me/theorems/b498918f-d12c-4ac9-bed4-d9fc8929e2d7
-- title:
--   At a candidate u, with Roy's strong six exponentials theorem as hypothesis: for |λ| = 1 algebraic and real f with 1, u, ū, f, f/(|u| + λu) free, f and f/(|u| + λu) are not both in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`), $\lambda \in \overline{\mathbb{Q}}$ with $|\lambda| = 1$, and $f$ real with $1, u, \bar u, f, f/(|u| + \lambda u)$ free over $\overline{\mathbb{Q}}$. Then $f$ and $f/(|u| + \lambda u)$ are not both in $\widetilde{\mathcal{L}}$. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** At a candidate $u \notin \overline{\mathbb{Q}}$ (`DiazModulus.hermite_lindemann_holds`), $s = |u|$ is algebraic and real with $s^2 = u\bar u$, and $u, \bar u \in \mathcal{L}$ (`DiazModulus.logAlg_conj_stable`). If $f$ and $g$ are in $\widetilde{\mathcal{L}}$, then so is $W$, and the configuration of `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration` contradicts `hSSE`.
--
--   **Novelty.** Not asserted: it is one substitution in Diaz (2007, Th. 7(1)), with v₀ = f/(|u| + λu); Diaz (2004, Th. 2) at x = (v₀, v̄₀) also gives it.
-- source:
--   One substitution in G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(1) (p. 390); also G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538). Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2) is carried as a hypothesis. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_real_pencil_not_both_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (f : ℂ) (hf : conj f = f)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, f, f / (((‖u‖ : ℝ) : ℂ) + lam * u)]) :
    ¬ (f ∈ LogAlgTilde ∧ f / (((‖u‖ : ℝ) : ℂ) + lam * u) ∈ LogAlgTilde) := by
  sorry

end DiazModulus
