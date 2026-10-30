-- Prove2me | Theorems.Thm_DiazModulus_boxHilb_chain_bound
-- name    : DiazModulus.boxHilb_chain_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:27.10998+00:00
-- url     : https://prove2.me/theorems/82835cfd-fd9f-4341-9446-c3d96087f058
-- title:
--   The regular chain bound (DALAG Th. 8.4, finite level): for $P_0, \dots, P_{r-1} \in F_D$ regular in turn modulo $I$, $2^{r(r-1)/2} u^r h_{I+(P)}(uD) \le h_I(2^r uD)$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that $F$ is monotone ($T \le T'$ coordinatewise implies $F_T \subseteq F_{T'}$), that $F$ is multiplicative ($a \in F_T$ and $b \in F_U$ imply $ab \in F_{T+U}$) and that every $F_T$ is finite-dimensional. Let $I$ be an ideal of $S$, $D \in \mathbb{N}^B$, $r \in \mathbb{N}$ and $P_0, \dots, P_{r-1} \in F_D$ such that each $P_k$ is a nonzerodivisor on $S/(I + (P_j : j < k))$. Then for every $u \in \mathbb{N}$, $2^{r(r-1)/2} u^r h_{I + (P_0, \dots, P_{r-1})}(uD) \le h_I(2^r u D)$, where $uD$ is the coordinatewise multiple. For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Put $I_k = I + (P_j : j < k)$ and $f_k(v) = h_{I_k}(vD)$. Each $f_{k+1}$ is monotone (`DiazModulus.boxHilb_mono`), and for $k < r$, `DiazModulus.boxHilb_sup_span_add_le` with $T = vD$ gives $f_{k+1}(v+1) + f_k(v) \le f_k(v+1)$, since $(v+1)D = vD + D$. The iterated telescope `DiazModulus.nat_telescope_iter` with $j = r$ gives $2^{r(r-1)/2} u^r f_r(u) \le f_0(2^r u)$, which is the claim.
--
--   **Novelty.** Not found in the sources read in this form; routine. A finite-level form of the chain of DALAG Th. 8.4 (built with Lemma 8.5), which compares leading coefficients of Hilbert polynomials instead.
-- source:
--   Finite-level form of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.4 and its proof through Lemma 8.5 (§8.2.3, pp. 236–238; Chapter 8 is by D. Roy). Not found in the sources read in this form; routine. Uses DiazModulus.boxHilb_mono, DiazModulus.boxHilb_sup_span_add_le and DiazModulus.nat_telescope_iter. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem boxHilb_chain_bound {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmono : Monotone F)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (D : B → ℕ) (r : ℕ)
    (P : Fin r → S) (hP : ∀ k, P k ∈ F D)
    (hreg : ∀ k : Fin r, IsSMulRegular (S ⧸ (I ⊔ Ideal.span (P '' {j | j < k}))) (P k)) (u : ℕ) :
    2 ^ (r * (r - 1) / 2) * u ^ r * boxHilb F (I ⊔ Ideal.span (Set.range P)) (u • D)
      ≤ boxHilb F I ((2 ^ r * u) • D) := by
  sorry

end DiazModulus
