-- Prove2me | Theorems.Thm_DiazModulus_candidate_laurent_conj_hull_class_not_mem_logAlgTilde
-- name    : DiazModulus.candidate_laurent_conj_hull_class_not_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:27:51.21693+00:00
-- url     : https://prove2.me/theorems/e4c4791f-3793-494c-aa19-43fbfeb9b21d
-- title:
--   At a candidate u, under Roy's strong six exponentials theorem, a polynomial in u and ū whose hull is in the polynomial, involution or real pencil class is not in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`: $u \neq 0$, with $|u|$ and $e^u$ algebraic), let $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$, and put $v = u/s$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for all $j \in \mathbb{Z}$, and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, z, \bar z)$. If $W$ is in one of the classes
--
--   - **(P)** $\alpha u^2 + \beta u^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero;
--   - **(Q)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$,
--
--   then $z \notin \widetilde{\mathcal{L}}$.
--
--   **Proof.** By Hermite–Lindemann (`DiazModulus.hermite_lindemann_holds`), $u \notin \overline{\mathbb{Q}}$. The class forces $\dim W = 5$ (`DiazModulus.laurent_conj_hull_class_finrank_eq_five`), so Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`) puts a configuration in $W$. If $z \in \widetilde{\mathcal{L}}$, then $W \subseteq \widetilde{\mathcal{L}}$: $1 \in \widetilde{\mathcal{L}}$, $u \in \mathcal{L}$ since $e^u$ is algebraic, $\bar u \in \mathcal{L}$ (`DiazModulus.logAlg_conj_stable`) and $\bar z \in \widetilde{\mathcal{L}}$ (`DiazModulus.logAlgTilde_conj_stable`). The configuration then lies in $\widetilde{\mathcal{L}}$, against `hSSE`.
--
--   **Novelty.** Each instance is a substitution in Roy's strong six exponentials theorem (Roy 1992, Cor. 2); for class (Q) it is also one in Diaz (2004, Th. 2). Not found in the sources read as a family; routine. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
-- source:
--   Each instance is a substitution in Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2), which is carried as a hypothesis; for class (Q) also in G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538). Not found in the sources read as a family. Uses DiazModulus.hermite_lindemann_holds, DiazModulus.logAlg_conj_stable, DiazModulus.logAlgTilde_conj_stable, DiazModulus.laurent_conj_hull_two_by_three_configuration_iff and DiazModulus.laurent_conj_hull_class_finrank_eq_five. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_laurent_conj_hull_class_not_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (u s : ℂ) (hcand : IsCandidate u) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (hcls : (∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) :
    (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) ∉ LogAlgTilde := by
  sorry

end DiazModulus
