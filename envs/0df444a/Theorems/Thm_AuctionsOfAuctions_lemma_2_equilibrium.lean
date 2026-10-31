-- Prove2me | Theorems.Thm_AuctionsOfAuctions_lemma_2_equilibrium
-- name    : AuctionsOfAuctions.lemma_2_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:31.996775+00:00
-- url     : https://prove2.me/theorems/5b11e54f-bbb2-4d0d-8033-b14235f6cb95
-- title:
--   Lemma 2, eq. (13): $\tilde\sigma(\cdot;R)$ is the exchanges' (unique increasing) symmetric equilibrium bid
-- statement:
--   Two exchanges each represent two advertisers. An exchange whose highest advertiser valuation is $m\ge R$ receives its internal first-price auction's winning bid $\beta(m;R)$ and bids in the publisher's header auction with reserve $R$; the rival exchange's type $m'$ has law $F^2$, stays out when $m'<R$ and otherwise bids $\sigma(m')$. Bidding $s\ge R$ earns
--   $$U_\sigma(s,m)=P\big(m'<R\ \text{or}\ \sigma(m')<s\big)\,\big(\beta(m;R)-s\big).$$
--   For every reserve $R\in[0,1]$:
--
--   1. the strategy $\tilde\sigma(\cdot;R)$ of (13),
--   $$\tilde\sigma(m;R)=\frac{RF^2(R)}{F^2(m)}+\frac{1}{F^2(m)}\int_R^m\beta(y;R)\,dF^2(y),$$
--   is a symmetric equilibrium: for every type $m\in[R,1]$, $\tilde\sigma(m;R)\ge R$ and $U_{\tilde\sigma}(s,m)\le U_{\tilde\sigma}(\tilde\sigma(m;R),m)$ for every bid $s\ge R$;
--   2. every strictly increasing (on $[R,1]$) symmetric equilibrium $\sigma$ satisfies $\sigma(m)=\tilde\sigma(m;R)$ for every type $m\in[R,1]$ with $m>0$.
--
--   The closed form (13), in terms of the exchange's highest underlying valuation, is what makes the publisher's revenue (18) computable.
--
--   Differences from the source:
--   - reading: valuations drawn iid from a distribution $F$ with support $[0,1]$ (p.7) → $F(x)=\int_0^x f$, with $f$ continuous on $[0,1]$, $f\ge0$ on $[0,1]$, $f>0$ on $(0,1)$ and $\int_0^1 f=1$; reason: the paper writes $f=F'$, divides by $f(x)$ for $x\in(0,1)$ and differentiates its revenue integrals in $R$ (A18), which uses a continuous density; $f(0)=0$ and $f(1)=0$ are allowed
--   - encoding: Stieltjes integrals $\int g\,dF^k$ in (3), (4), (5), (13), (18) → $\int g(x)\,kF(x)^{k-1}f(x)\,dx$ (interval integrals); reason: $F$ is absolutely continuous with density $f$; same instances
--   - generalization: the standing assumption that $F$ is regular (p.7) → not assumed; reason: the statement holds for every distribution of the model; regular distributions are instances
--   - encoding: a reserve price $R$ → $R\in[0,1]$; reason: valuations lie in $[0,1]$: a reserve below $0$ acts as $0$ and a reserve above $1$ sells nothing, so the publisher's choice set is $[0,1]$
--   - reading: "The exchanges' bidding strategy … is $\tilde\sigma(m;R)$" → $\tilde\sigma$ is a symmetric equilibrium (best response to itself against every bid $s\ge R$), and every strictly increasing symmetric equilibrium equals $\tilde\sigma$ at every type $m\in[R,1]$ with $m>0$; reason: existence and uniqueness is the stronger reading; the paper's derivation (A33)–(A39) is the necessity direction for increasing strategies, and at $m=R=0$ the zero type wins with probability $F(0)^2=0$, so its bid is not determined
--   - encoding: the header auction (11)–(12) in terms of the internal winning bid $w$ and its law $H$ → in terms of types: the rival's type $m'$ has density $2F(m')f(m')$ on $[0,1]$, bids $\sigma(m')$ if $m'\ge R$ and stays out otherwise; ties lose; reason: the paper itself works with types (fn. 17, A1.10); $w=\beta(m;R)$ is strictly increasing, and ties are null events under a strictly increasing rival strategy
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §3.3, Lemma 2, eq. (13), p.13 (PDF 14); game (11)–(12), pp.12–13; proofs A1.3 and A1.10, pp.37, 42–43

import Mathlib
import Definitions.Def_AuctionsOfAuctions_Model

namespace AuctionsOfAuctions

/-- **Lemma 2, eq. (13): the exchanges' equilibrium bid**, Zeithammer–Choi, *Auctions of Auctions*,
Management Science (2024), doi:10.1287/mnsc.2024.05233, §3.3, p.13 (PDF 14); proof in A1.3, A1.10
(pp.37, 42–43): "The exchanges' bidding strategy, in terms of the highest valuation `m` among the
two advertisers the exchange represents, is `σ̃(m; R)`" of (13).

For every reserve `R ∈ [0, 1]`:
(a) `σ̃(·; R)` is a symmetric equilibrium of the exchanges' header auction (no type `m ∈ [R, 1]`
gains by deviating to any bid `s ≥ R` when the rival exchange bids `σ̃`);
(b) every strictly increasing symmetric equilibrium `σ` agrees with `σ̃(·; R)` at every type
`m ∈ [R, 1]` with `m > 0`.

**Formalization Note.** The lemma is read as existence and uniqueness (among strictly increasing
strategies, as the paper's derivation presumes "as long as the exchange bidding function is
increasing", p.12). At `m = R = 0` the bid of the zero type is not determined (it wins with
probability `F(0)² = 0`), hence `m > 0` in (b). -/
theorem lemma_2_equilibrium (D : ValuationDist) (R : ℝ) (hR : R ∈ Set.Icc (0 : ℝ) 1) :
    D.IsSymmetricEquilibrium R (fun m => D.sigmaTilde m R) ∧
    ∀ σ : ℝ → ℝ, StrictMonoOn σ (Set.Icc R 1) → D.IsSymmetricEquilibrium R σ →
      ∀ m ∈ Set.Icc R 1, 0 < m → σ m = D.sigmaTilde m R := by sorry

end AuctionsOfAuctions
