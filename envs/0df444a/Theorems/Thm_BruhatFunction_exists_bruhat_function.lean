-- Prove2me | Theorems.Thm_BruhatFunction_exists_bruhat_function
-- name    : BruhatFunction.exists_bruhat_function
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:42:59.831992+00:00
-- url     : https://prove2.me/theorems/06cd8542-bb30-4605-bd38-3e87451c6d7d
-- title:
--   Existence of a Bruhat function: a continuous $u\ge 0$ on $G$ with $\int_H u(xh)\,d\mu_H(h)=1$ for all $x$, for a closed subgroup $H$ of a locally compact group $G$
-- statement:
--   **Existence of a Bruhat function.** Let $G$ be a locally compact Hausdorff topological group, let $H\le G$ be a closed subgroup, let $\pi\colon G\to G/H$ be the projection onto the space of left cosets $xH$, and let $\mu_H$ be a left Haar measure on $H$. Then there is a function $u\colon G\to\mathbb R$ with the following properties.
--
--   1. $u$ is continuous and $u(x)\ge 0$ for all $x\in G$.
--   2. For every compact set $K\subseteq G$ the set $\operatorname{supp}(u)\cap KH$ is compact. Here $KH=\pi^{-1}(\pi(K))$ is the union of the cosets that meet $K$.
--   3. For every $x\in G$ the function $h\mapsto u(xh)$ is $\mu_H$-integrable on $H$, and
--   $$\int_H u(xh)\,d\mu_H(h)=1 .$$
--
--   Such a function is called a *Bruhat function* for $H$. It is the standard tool for passing between functions on $G$ and on $G/H$. For a continuous function $v$ on $G/H$, property 3 gives $\int_H u(xh)\,v(\pi(xh))\,d\mu_H(h)=v(\pi(x))$, because $v\circ\pi$ is constant on cosets. So $v\mapsto u\cdot(v\circ\pi)$ is a right inverse of the coset-integration map $f\mapsto\big(xH\mapsto\int_H f(xh)\,d\mu_H(h)\big)$, and Bruhat functions are used to build invariant and quasi-invariant measures on $G/H$. In the paper (Lemma 12.2.1.1, where such a function is called an *$H$-indentation*, Definition 12.2.1.3) it is used to construct the isometric section $\Psi_{u_0}$ of Corollary 12.2.1.2. It is also used to lift kernels from $G/H\times G/H$ to $G\times G$ (Proposition 12.2.2.2), eventually for $G=\mathrm{GL}_1(\mathbf A_F)$ and $H=F^\times$.
--
--   **Deviation from the source.** The paper states the lemma for second-countable Hausdorff locally compact *abelian* groups and writes the coset integral as $\int_H u_0(h^{-1}x)\,d\mu_H(h)$. Here we state the general form of the construction it cites (any locally compact group, no countability assumption). For abelian $G$ we have $h^{-1}x=xh^{-1}$, and Haar measure on the abelian group $H$ is invariant under inversion, so the two normalizations agree. The paper's last assertion, that $\int_H (u_0\cdot(v\circ\pi))(h^{-1}x)\,d\mu_H(h)=v(\pi(x))$ for continuous $v$ on $G/H$, follows from property 3 as explained above.
--
--   **Formalization Note.** $KH$ is the pointwise product `K * (H : Set G)`, and the support is the closed support `tsupport u`. $\mu_H$ is any measure on the subtype `H` (carrying a Borel $\sigma$-algebra) that is a left Haar measure. Integrability in 3 is asserted explicitly, so the Bochner integral is not a junk value.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 504–505, Lemma 12.2.1.1; classical reference: N. Bourbaki, Elements of Mathematics, Integration II, Ch. VII, §2, no. 4, Prop. 8 (INT VII.37), cited by the paper at this lemma

import Mathlib

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace BruhatFunction

/-- Existence of a continuous Bruhat function for a closed subgroup `H` of a locally compact
group `G`: a continuous `u ≥ 0` on `G` whose support meets every saturated set `K * H`
(`K` compact) in a compact set, and whose integral over every left coset `x * H` against a
left Haar measure of `H` equals `1`. -/
theorem exists_bruhat_function
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsHaarMeasure] :
    ∃ u : G → ℝ, Continuous u ∧ (∀ x, 0 ≤ u x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport u ∩ (K * (H : Set G)))) ∧
      ∀ x : G, Integrable (fun h : H => u (x * (h : G))) μH ∧
        ∫ h : H, u (x * (h : G)) ∂μH = 1 := by sorry

end BruhatFunction
