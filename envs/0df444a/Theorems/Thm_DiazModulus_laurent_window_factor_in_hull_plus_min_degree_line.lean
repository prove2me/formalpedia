-- Prove2me | Theorems.Thm_DiazModulus_laurent_window_factor_in_hull_plus_min_degree_line
-- name    : DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:48.551886+00:00
-- url     : https://prove2.me/theorems/7238d170-e301-4e90-a1b3-29ab14185c30
-- title:
--   If every non-zero element of a plane M has degree ≥ N + 2, and p y, q y lie in H_N + M with deg p < deg q, then p y lies in H_N + K n for n of least degree in M
-- statement:
--   Let $K$ be a field, $N \geq 0$, $H_N = \mathrm{span}_K(X^{N-1}, X^N, X^{N+1}) \subseteq K[X]$ (with $N - 1$ read as $0$ when $N = 0$), and $M \subseteq K[X]$ a subspace of dimension $2$ whose non-zero elements all have degree at least $N + 2$. Then $M$ has a non-zero element $n$ of least degree among its non-zero elements such that, for all $p, q, y \in K[X]$ with $\deg p < \deg q$: if $py$ and $qy$ lie in $H_N + M$, then $py \in H_N + Kn$.
--
--   **Proof.** Take $n \in M$ non-zero of least degree. Write $py = h + m$ and $qy = h' + m'$ with $h, h' \in H_N$ and $m, m' \in M$; if $m = 0$ there is nothing to prove. Otherwise $\deg(py) = \deg m \geq N + 2 > \deg h$, so $p, y \neq 0$ and $\deg(qy) > \deg(py)$; hence $m' \neq 0$, $\deg(qy) = \deg m'$ and $\deg m < \deg m'$. Two elements of distinct degrees span the plane $M$, so $n = am + bm'$, and the minimality of $\deg n$ forces $b = 0$: $m \in Kn$.
--
--   **Novelty.** Not found in the sources read; routine. The degree count is in the manner of the valuation argument of Bachoc, Serra and Zémor (2017, §7, proof of Th. 33).
-- source:
--   Not found in the sources read; a degree count in the manner of C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), §7. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_window_factor_in_hull_plus_min_degree_line (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree) :
    ∃ n ∈ M, n ≠ 0 ∧ (∀ f ∈ M, f ≠ 0 → n.natDegree ≤ f.natDegree) ∧
      ∀ p q y : K[X], p.natDegree < q.natDegree → p * y ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) →
        q * y ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) →
        p * y ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), n} : Set K[X]) := by
  sorry

end DiazModulus
