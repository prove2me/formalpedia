-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiDihedrant_example_6_2
-- name    : EdgeTransBiCayley.BiDihedrant.example_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:38:01.027811+00:00
-- url     : https://prove2.me/theorems/b3fbf884-be42-42b1-8b68-b74170ef5128
-- title:
--   Example 6.2, p. 13 — Γ(n, λ, 2k) is connected, 2k-valent and normal edge-transitive
-- statement:
--   Assume the hypotheses of Example 6.2: $n \ge 5$, $k \ge 2$, $\lambda \in \mathbb Z_n^*$ of order $2k$, and $1 + \lambda^2 + \cdots + \lambda^{2(k-1)} \equiv 0 \pmod n$. Let $S = S(n,\lambda,2k)$, $\Gamma = \Gamma(n,\lambda,2k)$ and $X = N_{\mathrm{Aut}(\Gamma)}(R(D_n))$. Then:
--
--   1. $\Gamma$ is connected;
--   2. $|S| = 2k$, and every vertex of $\Gamma$ has degree $2k$;
--   3. $c_{k-1} \equiv d_{k-1} \equiv 0 \pmod n$, and $1 + \lambda d_i \equiv c_{i+1} \pmod n$ for all $i \in \mathbb Z_k$ (indices mod $k$);
--   4. the automorphism $\alpha$ of $D_n$ with $(a, b) \mapsto (a^\lambda, ba)$ satisfies $S^\alpha = bS$; the permutation $\sigma_{\alpha,b}$ is an automorphism of $\Gamma$ in $X$, it fixes $1_0$, and it maps $(a^{c_i})_1 \mapsto (ba^{d_i})_1 \mapsto (a^{c_{i+1}})_1$ for all $i \in \mathbb Z_k$, so it permutes the $2k$ neighbours of $1_0$ cyclically;
--   5. $X$ is transitive on the edges of $\Gamma$:
--
--   $$
--   \Gamma(n,\lambda,2k) \text{ is normal edge-transitive.}
--   $$
--
--   These are the facts on which Proposition 6.4 builds the semisymmetric examples.
--
--   **Formalization Note** $a = $ `r 1`, $b = $ `sr 0`, $ba = $ `sr 1`, $a^\lambda = $ `r λ` in `DihedralGroup n`; $bS$ is the pointwise product `sr 0 • S`. The index $i+1$ is taken mod $k$, as the paper's $i \in \mathbb Z_k$ requires. Normal edge-transitivity is edge-transitivity of the subgroup $X$ of the full automorphism group, not of $\mathrm{Aut}(\Gamma)$.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 13, Example 6.2 (claims following the definition)

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiDihedrant_Gamma
open Pointwise

namespace EdgeTransBiCayley.BiDihedrant

theorem example_6_2 (n lam k : ℕ) [NeZero n] (h : Ex62Hyp n lam k) :
    (gammaData n lam k).graph.Connected ∧
    (gammaS n lam k).card = 2 * k ∧
    (∀ v, (gammaData n lam k).graph.degree v = 2 * k) ∧
    ((cParam lam (k - 1) : ZMod n) = 0 ∧ (dParam lam (k - 1) : ZMod n) = 0) ∧
    (∀ i ∈ Finset.range k,
      (1 + (lam : ZMod n) * (dParam lam i : ZMod n)) = (cParam lam ((i + 1) % k) : ZMod n)) ∧
    (∃ α : MulAut (DihedralGroup n),
      α (DihedralGroup.r (1 : ZMod n)) = DihedralGroup.r (lam : ZMod n) ∧
      α (DihedralGroup.sr (0 : ZMod n)) = DihedralGroup.sr (1 : ZMod n) ∧
      (gammaS n lam k).image α = DihedralGroup.sr (0 : ZMod n) • gammaS n lam k ∧
      (∃ φ ∈ normRH (gammaData n lam k), ∀ v, φ v = sigmaPerm α (DihedralGroup.sr (0 : ZMod n)) v) ∧
      sigmaPerm α (DihedralGroup.sr (0 : ZMod n)) (.inl (1 : DihedralGroup n)) = .inl (1 : DihedralGroup n) ∧
      ∀ i ∈ Finset.range k,
        sigmaPerm α (DihedralGroup.sr (0 : ZMod n)) (.inr (DihedralGroup.r (cParam lam i : ZMod n))) =
            .inr (DihedralGroup.sr (dParam lam i : ZMod n)) ∧
        sigmaPerm α (DihedralGroup.sr (0 : ZMod n)) (.inr (DihedralGroup.sr (dParam lam i : ZMod n))) =
            .inr (DihedralGroup.r (cParam lam ((i + 1) % k) : ZMod n))) ∧
    IsEdgeTransitiveOn (gammaData n lam k).graph (normRH (gammaData n lam k)) := by sorry

end EdgeTransBiCayley.BiDihedrant
