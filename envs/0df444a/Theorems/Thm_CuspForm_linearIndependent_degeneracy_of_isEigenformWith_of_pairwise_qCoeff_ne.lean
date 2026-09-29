-- Prove2me | Theorems.Thm_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
-- name    : CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/c4796562-85fe-56a1-9020-53cfd804fd36
-- title:
--   Linear independence of degeneracy images of Hecke eigenforms
-- statement:
--   Fix a nonzero level $M$, a weight $k \in \mathbb{Z}$, a natural number $n$, and nonzero levels $L_i$ for $i \in \mathrm{Fin}\,n$ with $L_i \mid M$, together with Dirichlet characters $\varepsilon_i$ modulo $L_i$ with values in $\mathbb{C}$ and cusp forms $g_i$ of weight $k$ on $\Gamma_1(L_i)$. Assume each $g_i$ satisfies [`CuspForm.IsEigenformWith`](def/CuspForm_PrimitiveFormGamma1.html#L19) for $\varepsilon_i$, i.e. writing $a_m(g_i)$ for the $m$-th coefficient of the $q$-expansion of width $1$: $a_1(g_i) = 1$; for every prime $p \nmid L_i$ and every $m$, $a_{pm}(g_i) + \varepsilon_i(p) p^{k-1} a_{m/p}(g_i)$ (the last term read as $0$ unless $p \mid m$) equals $a_p(g_i) a_m(g_i)$; for every prime $\ell \mid L_i$ and every $m$, $a_{\ell m}(g_i) = a_\ell(g_i) a_m(g_i)$; and $g_i$ has nebentypus $\varepsilon_i$, meaning $g_i(\gamma \tau) = \varepsilon_i(\gamma_{11})(\gamma_{10}\tau + \gamma_{11})^k g_i(\tau)$ for all $\gamma \in \Gamma_0(L_i)$ and $\tau \in \mathcal{H}$. Assume the $g_i$ are pairwise separated away from $M$: for $i \neq j$ there is a prime $p \nmid M$ with $a_p(g_i) \neq a_p(g_j)$. Let $G_{i,d}$ be cusp forms of weight $k$ on $\Gamma_1(M)$ such that, for every $d \mid M/L_i$, $G_{i,d}(\tau) = g_i(\mathrm{heckeDiagMatrix}(d) \cdot \tau)$, where $\mathrm{heckeDiagMatrix}(d)$ is the class of $\begin{pmatrix} d & 0 \\ 0 & 1\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$ for $d \neq 0$ (and the identity for $d = 0$), so that $G_{i,d}(\tau) = g_i(d\tau)$. Then for any complex scalars $c_{i,d}$ with $\sum_i \sum_{d \mid M/L_i} c_{i,d} G_{i,d} = 0$ one has $c_{i,d} = 0$ for every $i$ and every divisor $d$ of $M/L_i$.
--
--   This is the linear-independence (direct-sum) half of the Atkin–Lehner–Li decomposition of a space of cusp forms into the degeneracy images of eigenforms of lower level. It is combined with the corresponding spanning statement in [`CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus`](thm.html#CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
    (M : ℕ) [NeZero M] (k : ℤ) (n : ℕ) (L : Fin n → ℕ) [∀ i, NeZero (L i)] (hL : ∀ i, L i ∣ M)
    (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
    (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
    (hg : ∀ i, CuspForm.IsEigenformWith (ε i) (g i))
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧
      ModularFormClass.qCoeff (g i) p ≠ ModularFormClass.qCoeff (g j) p)
    (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
      ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ))
    (c : Fin n → ℕ → ℂ)
    (hc : (∑ i, ∑ d ∈ Nat.divisors (M / L i), c i d • G i d) = 0) :
    ∀ (i : Fin n), ∀ d ∈ Nat.divisors (M / L i), c i d = 0 := by sorry
