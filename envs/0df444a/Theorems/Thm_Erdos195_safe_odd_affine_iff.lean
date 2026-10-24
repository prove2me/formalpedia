-- Prove2me | Theorems.Thm_Erdos195_safe_odd_affine_iff
-- name    : Erdos195.safe_odd_affine_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T13:11:11.753496+00:00
-- url     : https://prove2.me/theorems/3476741b-5a9c-46e6-9e90-97cc80942d44
-- title:
--   Odd affine maps $x\mapsto mx+s$ transport tree orders and tree safety exactly
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1 \Leftrightarrow \theta(k,\,x\bmod 2^k)=1$ ($\mathrm{bit}_k$ is the $k$-th two's-complement binary digit). A finite word $Q$ of integers is $\theta$-safe if the completion "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression (positions of $a,a+r,a+2r,a+3r$ increasing, $r\neq0$). Positions in $Q$ are first occurrences. Let $m$ be an odd integer (of either sign) and $s$ any integer, and let $f(x)=mx+s$. Call $\theta'$ an $f$-transport of $\theta$ if for every $k$ and every $0\le r<2^k$
--
--   $$\theta'\big(k,\,(mr+s)\bmod 2^k\big)=\theta(k,r)\ \oplus\ \mathrm{bit}_k(mr+s).$$
--
--   Then (1) an $f$-transport exists (it is unique on the residues $0\le\rho<2^k$, since $r\mapsto (mr+s)\bmod 2^k$ is a bijection of $\{0,\dots,2^k-1\}$); and for every $f$-transport $\theta'$: (2) $f$ is an order isomorphism, $x\prec_\theta y\iff f(x)\prec_{\theta'}f(y)$; (3) for every finite word $Q$, $Q$ is $\theta$-safe iff $f(Q)=(f(q_1),f(q_2),\dots)$ is $\theta'$-safe.
--
--   So tree safety is exactly invariant under the odd affine group $x\mapsto mx+s$; with $m=-1$ this is the mirror $x\mapsto s-x$, under which an open pair of $Q$ at node $(k,a\bmod 2^k)$ becomes an open pair of $s-Q$ at node $(k,(s-a)\bmod 2^k)$. Together with the scaling lemma for $x\mapsto 2x+c$ this covers all maps $x\mapsto 2^j m x+s$.
--
--   Formalization note: the xor condition is written as $\theta'(\dots)=1\iff(\theta(k,r)=1\iff\neg\,\mathrm{bit}_k(mr+s)=1)$; `%` is `Int.emod`; `bitOne x k` is $\lfloor x/2^k\rfloor\bmod 2=1$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; statement and Lean proof by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem safe_odd_affine_iff (θ : ℕ → ℤ → Bool) (m s : ℤ) (hm : m % 2 = 1) :
    (∃ θ' : ℕ → ℤ → Bool, ∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
        (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))) ∧
    ∀ θ' : ℕ → ℤ → Bool, (∀ (k : ℕ) (r : ℤ), 0 ≤ r → r < 2 ^ k →
        (θ' k ((m * r + s) % 2 ^ k) = true ↔ (θ k r = true ↔ ¬ bitOne (m * r + s) k))) →
      (∀ x y : ℤ, treeLt θ x y ↔ treeLt θ' (m * x + s) (m * y + s)) ∧
      (∀ Q : List ℤ, Safe (treeLt θ) Q ↔ Safe (treeLt θ') (Q.map (fun x => m * x + s))) := by sorry

end Erdos195
